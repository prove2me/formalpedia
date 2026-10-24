-- Prove2me | Theorems.Thm_KellyStochasticNetworks_MaxWeight_foster_lyapunov
-- name    : KellyStochasticNetworks.MaxWeight.foster_lyapunov
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-22T03:49:16.004722+00:00
-- url     : https://prove2.me/theorems/2b764bc8-a49d-4699-907e-120db083640b
-- title:
--   Proposition D.1 — Foster–Lyapunov criterion with a finite exception set
-- statement:
--   Let $P$ be an irreducible homogeneous Markov chain on a nonempty countable state space $S$. Suppose $L:S\to[0,\infty)$, $\epsilon>0$, $b\in\mathbb R$, and a finite set $K\subseteq S$ satisfy, at every state $i$,
--   $$\mathbb E[L(X_{n+1})-L(X_n)\mid X_n=i]\le\begin{cases}-\epsilon,&i\notin K,\\b-\epsilon,&i\in K.\end{cases}$$
--   Then the expected first visit to $K$ after time zero is finite from every starting state, and the chain is positive recurrent:
--   $$\forall i\in S,\quad \mathbb E_i[\tau_K^+]<\infty,\qquad \mathbb E_i[\tau_{\{i\}}^+]<\infty.$$
--   This supplies the recurrence criterion for the queue chain. No aperiodicity assumption is imposed.
--
--   **Formalization Note** The conditional expectations are row sums of the transition kernel. Absolute summability of the increment is explicit, encoding the finiteness already forced by the printed drift bound and the nonnegativity of $L$. Hitting times start at time one, including when the initial state lies in $K$.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed pp. 210–211 (PDF pp. 218–219), Proposition D.1; DOI 10.1017/cbo9781139565363

import Definitions.Def_KellyStochasticNetworks_MaxWeight_Chain

open scoped ENNReal
open Classical

open scoped NNReal

/- Imported dependency source, reproduced verbatim for standalone inspection.
/-- A discrete-time transition law on a countable state space. -/
def Chain (S : Type*) := S → PMF S

/-- Probability of reaching `j` in exactly `n` transitions from `i`. -/
noncomputable def transitionPower {S : Type*} (P : Chain S) : ℕ → S → S → ℝ≥0∞
  | 0, i, j => if i = j then 1 else 0
  | n + 1, i, j => ∑' k, P i k * transitionPower P n k j

/-- Every state communicates with every other state. -/
def Irreducible {S : Type*} (P : Chain S) : Prop :=
  ∀ i j, ∃ n : ℕ, 0 < transitionPower P n i j

/-- Probability that times 1 through n all avoid K, starting from i at time 0. -/
noncomputable def avoidProbability {S : Type*} (P : Chain S) (K : Set S) :
    ℕ → S → ℝ≥0∞
  | 0, _ => 1
  | n + 1, i => ∑' j, if j ∈ K then 0 else P i j * avoidProbability P K n j

/-- Extended expected strictly positive hitting time, using the tail-sum formula.
Non-return has infinite cost, even if it occurs with positive probability less than one. -/
noncomputable def meanReturn {S : Type*} (P : Chain S) (K : Set S) (i : S) : ℝ≥0∞ :=
  ∑' n : ℕ, avoidProbability P K n i

/-- Every state has finite expected strictly positive return time. -/
def PositiveRecurrent {S : Type*} (P : Chain S) : Prop :=
  ∀ i, meanReturn P {i} i < ∞

/-- Real one-step drift; use only with the separately asserted absolute summability. -/
noncomputable def drift {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : ℝ :=
  ∑' j, (P i j).toReal * (L j - L i)

/-- Absolute integrability of a one-step increment on the countable state space. -/
def DriftIntegrable {S : Type*} (P : Chain S) (L : S → ℝ) (i : S) : Prop :=
  Summable (fun j => (P i j).toReal * |L j - L i|)
-/

namespace KellyStochasticNetworks.MaxWeight

theorem foster_lyapunov {S : Type*} [Countable S] [Nonempty S]
    (P : Chain S) (hirr : Irreducible P) (L : S → ℝ) (hL : ∀ i, 0 ≤ L i)
    (ε b : ℝ) (hε : 0 < ε) (K : Finset S)
    (hint : ∀ i, DriftIntegrable P L i)
    (hbound : ∀ i, drift P L i ≤ if i ∈ K then b - ε else -ε) :
    (∀ i, meanReturn P (K : Set S) i < ∞) ∧ PositiveRecurrent P := by sorry

end KellyStochasticNetworks.MaxWeight
