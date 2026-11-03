-- Prove2me | Theorems.Thm_MobilePromo_lemma_3
-- name    : MobilePromo.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:48.980282+00:00
-- url     : https://prove2.me/theorems/08e1427b-ffc0-4637-b393-3c4934fef3dc
-- title:
--   Lemma 3: the mean squared error of the MLE is $O(1/s)$
-- statement:
--   Let Assumptions 1 and 2 hold. There is a constant $K_{mle}>0$, independent of $I$ and $T$, such that for any $s\ge1$, the vector of maximum-likelihood estimates $\hat\gamma(s)=(\hat\gamma_1(s),\dots,\hat\gamma_L(s))$ based on $s$ i.i.d. repetitions of the exploration bids satisfies
--
--   $$
--   \mathbb E\bigl[\|\hat\gamma(s)-\gamma^{(0)}\|^2\bigr]\le\frac{K_{mle}}{s}
--   $$
--
--   for every $\gamma^{(0)}\in\Gamma^{(0)}$ and every choice among likelihood maximizers. This is the learning rate that the exploitation phases rely on.
--
--   Differences from the source:
--   - reading: "after $s$ exploration phases" under the heading "Mean-Squared Errors for MLE Based on IID Samples", with no assumption named → the expectation under the i.i.d. law `iidExp`, under Assumptions 1 and 2; reason: the heading and the proof (A9) treat i.i.d. data; `exploration_data_law` is the link to the policy
--   - generalization: constants "independent of $I$ and $T$" → the constants are also chosen before the schedule, the true parameter and the choice among likelihood maximizers; reason: the schedule varies with $I$, so the constants must not see it; the printed proof gives this (compactness of $[b^{\min}-e,0]\times\Gamma^{(0)}\times B$), and it specializes to the printed claim
--   - encoding: "there exist $k_l\in\mathbb N$ and a vector of exploration bids" (Assumption 2, p.12), the input of the policy (p.17) → the bids are the parameter `X : Exploration M`, with $k_l\ge 1$; reason: $\bar b_l$ is an input on p.17, and the phase needs a bid to place
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma 3, p.18; proof A9–A10 (PDF 43–44)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_Assumption2
import Definitions.Def_MobilePromo_MLESelector

set_option autoImplicit false

namespace MobilePromo

/-- Lemma 3 (SSRN 3523491, Lemma 3, p.18; proof A9–A10, PDF 43–44): there is `K_mle > 0`, independent of
`I` and `T`, such that for every `s ≥ 1`, `E[‖γ̂(s) - γ⁽⁰⁾‖²] ≤ K_mle / s`.

**Formalization Note** The expectation is over i.i.d. data (the heading "Mean-Squared Errors for MLE Based
on IID Samples", p.18); `exploration_data_law` links it to the data of the policy. `K_mle` is uniform in
`γ⁽⁰⁾ ∈ Γ⁽⁰⁾` and in the choice among maximizers. -/
theorem lemma_3 (M : Model) (h1 : Assumption1 M) (X : Exploration M) (h2 : Assumption2 M X) :
    ∃ Kmle : ℝ, 0 < Kmle ∧ ∀ (mle : MLESelector M X) (s : ℕ), 1 ≤ s → ∀ γ₀ ∈ M.Gamma0,
      iidExp M X γ₀ s (fun D => ‖mleVec M X mle s D - γ₀‖ ^ 2) ≤ Kmle / s := by sorry

end MobilePromo
