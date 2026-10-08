-- Prove2me | Theorems.Thm_KallenbergLP_Constrained_freq_eq_abel_limit
-- name    : KallenbergLP.Constrained.freq_eq_abel_limit
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:10.230968+00:00
-- url     : https://prove2.me/theorems/45ad87cf-9ca0-4db7-90a0-475a87b3a740
-- title:
--   Lemma 4.7.1 — for R in C_1 the frequency limit equals the Abel limit of discounted frequencies
-- statement:
--   Let $\beta$ be an initial distribution and $R$ a policy whose expected state-action frequencies $x^T(R)$ have exactly one limit point $x(R)$ (that is, $R\in C_1$). Then for every state $j$ and action $a\in A(j)$,
--
--   $$x_{ja}(R)=\lim_{\alpha\uparrow1}(1-\alpha)\sum_{t=1}^\infty\alpha^{t-1}\sum_i\beta_i\,\mathbb P_R(X_t=j,\ Y_t=a\mid X_1=i).$$
--
--   The lemma links the average-reward frequencies to normalized discounted frequencies, so that results for discounted problems can be transferred to the average case as the discount factor tends to one.
--
--   **Formalization Note** The limit $\alpha\uparrow1$ is taken along the left neighbourhood filter `𝓝[<] 1`; the Lean summation index $k$ is the book's $t-1$.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, pp. 153–154, Lemma 4.7.1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_KallenbergLP_Constrained_Frequencies

namespace KallenbergLP.Constrained

open MarkovDecisionProcesses Filter Topology

/-- Kallenberg (1983), Lemma 4.7.1, pp. 153–154: for `R ∈ C_1` with unique limit point `x(R)` and
every pair `(j, a)`,
`x_{ja}(R) = lim_{α↑1} (1−α) ∑_{t=1}^∞ α^{t−1} ∑_i β_i ℙ_R(X_t = j, Y_t = a | X_1 = i)`. -/
theorem freq_eq_abel_limit {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S]
    [DecidableEq A] (M : StationaryMDP S A) (β : S → ℝ) (hβ0 : ∀ j, 0 ≤ β j)
    (hβ1 : ∑ j, β j = 1) (R : AvgHRPolicy M) (hR : IsC1 β R)
    (x : KallenbergLP.AverageLP.Pair M → ℝ) (hx : x ∈ limitPoints β R) (p : KallenbergLP.AverageLP.Pair M) :
    Tendsto (fun α : ℝ => (1 - α) * ∑' k : ℕ, α ^ k * ∑ i, β i * prob R k i p)
      (𝓝[<] 1) (𝓝 (x p)) := by sorry

end KallenbergLP.Constrained
