-- Prove2me | Theorems.Thm_OnlineStochMatching_SuggestedMatching_theorem_4
-- name    : OnlineStochMatching.SuggestedMatching.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T22:03:29.968309+00:00
-- url     : https://prove2.me/theorems/5e29c5a0-4f2d-4e42-9569-850790269495
-- title:
--   Theorem 4 — suggested matching achieves a tight $1-1/e$ factor
-- statement:
--   Fix the suggested matching algorithm on any finite integer-frequency online stochastic matching instance. For every $\varepsilon>0$, there exist $\delta>0$ and $N$ independent of the instance, of which maximum integral flow is selected, and of its random-choice labelling such that, for $n\ge N$,
--
--   $$\Pr\!\left[\mathrm{ALG}\ge(1-e^{-1})\mathrm{OPT}-\varepsilon n\right]\ge1-e^{-\delta n}.$$
--
--   The factor is tight: on the complete bipartite family with $n\ge1$, every maximum expected-instance matching and every valid labelling have $\mathrm{OPT}=n$ in every scenario and $\mathbb E[\mathrm{ALG}]=n(1-(1-1/n)^n)$; the expected ratio tends to $1-e^{-1}$ as $n\to\infty$.
--
--   **Formalization Note** The paper states a high-probability approximation factor. Its proof yields the displayed additive error without assuming $\mathrm{OPT}=\Omega(n)$; a multiplicative ratio with an arbitrary small error follows when that further growth condition holds. The theorem keeps all integer $e_i\ge0$ and represents both arrival and algorithm randomness by independent uniform draws of labelled copies.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, p. 6, Theorem 4 and §4.1, Tightness of the Analysis

import Definitions.Def_OnlineStochMatching_SuggestedMatching_Algorithm

namespace OnlineStochMatching.SuggestedMatching

/-- Theorem 4: additive high-probability guarantee and a complete-graph family
whose exact expected ratio approaches `1 - 1/e`. -/
theorem theorem_4 :
    (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (A I : Type) [Fintype A] [Fintype I]
        (inst : Instance A I) (hn : N ≤ inst.n)
        (M : Finset (A × I)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option A) (hlabel : IsLabelling inst M label),
        runProbability inst (fun ω =>
          (1 - Real.exp (-1)) * (optimum inst ω : ℝ) - ε * (inst.n : ℝ) ≤
            (algorithm inst label ω : ℝ)) ≥
          1 - Real.exp (-δ * (inst.n : ℝ))) ∧
    (∀ (n : ℕ) (hn : 0 < n),
      let inst := completeInstance n hn
      ∀ (M : Finset (Fin n × Fin n)) (hM : IsMaxBMatching inst M)
        (label : inst.Copy → Option (Fin n)) (hlabel : IsLabelling inst M label),
        (∀ ω : Fin inst.n → inst.Copy, optimum inst ω = n) ∧
          expectedAlgorithm inst label =
            (n : ℝ) * (1 - (1 - 1 / (n : ℝ)) ^ n)) ∧
    Filter.Tendsto (fun n : ℕ => 1 - (1 - 1 / (n : ℝ)) ^ n)
      Filter.atTop (nhds (1 - Real.exp (-1))) := by sorry

end OnlineStochMatching.SuggestedMatching
