-- Prove2me | Theorems.Thm_MDPFinance_Bellman_flow_property
-- name    : MDPFinance.Bellman.flow_property
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T20:17:57.444365+00:00
-- url     : https://prove2.me/theorems/b0d1572f-4229-4cd3-81c0-96b205b4e515
-- title:
--   Corollary 2.3.9 — the flow property of the value function
-- statement:
--   Under the Structure Assumption (SAN), the value function satisfies not only the one-step
--   Bellman equation but the analogous relation over any intermediate horizon: for $n \le m \le N$
--   and every state $x$,
--
--   $$
--   V_n(x) = \sup_\pi \mathbb{E}^\pi_{n,x}\!\left[\sum_{k=n}^{m-1} r_k\bigl(X_k, f_k(X_k)\bigr) +
--   V_m(X_m)\right].
--   $$
--
--   That is, the optimal expected reward from $(n,x)$ equals the optimal expected reward accrued
--   up to an intermediate time $m$, plus the (already-optimal) value $V_m(X_m)$ collected from
--   there onward — a semigroup-type "flow" property of $V$, following directly from Theorem 2.3.8
--   by an induction on $m - n$ that repeatedly substitutes the one-step Bellman equation. It
--   underlies the informal Principle of Dynamic Programming (made precise for a fixed optimal
--   policy in Theorem 2.3.12): the value of following an optimal strategy from the start agrees
--   with the value of behaving optimally up to any intermediate horizon and then simply reading off
--   the value function from there.
--
--   **Formalization Note.** The right-hand side is `⨆ π : Policy M, EFromTo M π n m x (V M m)`,
--   the general accumulator-based expectation of `MDPFinance.Bellman.ValueFunction` with terminal
--   payoff `V M m` instead of `g_N`, so that the case $m = N$ recovers `V M n x = ⨆ π, Vpi M π n x`,
--   the definition of the value function itself.
--
--   **Formalization Note (moderation).** The Integrability Assumption (AN) of Section 2.2, which
--   the book assumes throughout, is carried as the explicit hypothesis `hAN`; without it the
--   expectations defining $V_n^\pi$ need not exist, and the extended-real integral's convention
--   for $\infty - \infty$ would make the statement's terms artefacts of that convention.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 24, Corollary 2.3.9

import Mathlib
import Definitions.Def_MDPFinance_Bellman_Model
import Definitions.Def_MDPFinance_Bellman_Policy
import Definitions.Def_MDPFinance_Bellman_Operators
import Definitions.Def_MDPFinance_Bellman_ValueFunction
import Definitions.Def_MDPFinance_Bellman_StructureAssumption

open MeasureTheory ProbabilityTheory MDPFinance.Bellman

namespace MDPFinance.Bellman

/-- Corollary 2.3.9 (Bäuerle–Rieder, p. 24, PDF 39), under the standing Integrability
Assumption (AN): let (SAN) be satisfied. If `n ≤ m ≤ N` then
`V_n(x) = sup_π 𝔼^π_{n,x}[Σ_{k=n}^{m-1} r_k(X_k,f_k(X_k)) + V_m(X_m)]` for all `x ∈ E`. -/
theorem flow_property {E A : Type*} [MeasurableSpace E] [MeasurableSpace A] {N : ℕ}
    (M : MarkovDecisionModel E A N) (hAN : IntegrabilityAssumption M)
    (IMs : ℕ → Set (E → EReal)) (Deltas : ℕ → Set (E → A))
    (hSAN : StructureAssumption M IMs Deltas) (n m : ℕ) (hnm : n ≤ m) (hm : m ≤ N) (x : E) :
    V M n x = ⨆ π : Policy M, EFromTo M π n m x (V M m) := by sorry

end MDPFinance.Bellman
