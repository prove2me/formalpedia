-- Prove2me | Theorems.Thm_MobilePromo_lemma_A1_v
-- name    : MobilePromo.lemma_A1_v
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:16:58.443211+00:00
-- url     : https://prove2.me/theorems/dfe843e4-7f69-4a45-96fb-e6e09eddd13d
-- title:
--   Lemma A.1(v): the gap of $f^l$ is at most quadratic
-- statement:
--   Under Assumption 1 there is $K_0>0$ such that for every location $l$, all $b_l\in B$ and all $(\alpha,\gamma_l)\in\mathcal U_{A\Gamma_l}$,
--
--   $$
--   f^l(b_l,\alpha,\gamma_l)-f^l(b_l^*(\alpha,\gamma_l),\alpha,\gamma_l)\le K_0\bigl(b_l-b_l^*(\alpha,\gamma_l)\bigr)^2 .
--   $$
--
--   This converts a bidding error into a cost of its square, which is the source of the $\sqrt I$ rate.
--
--   Differences from the source:
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, Lemma A.1(v), A2 (PDF 36); $K_0=\max_lK_0^l$, A3 (PDF 37)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Lemma A.1(v) (SSRN 3523491, Lemma A.1(v), A2, PDF 36): there is `K₀ > 0` with
`f^l(b_l, α, γ_l) - f^l(b*_l(α, γ_l), α, γ_l) ≤ K₀ (b_l - b*_l(α, γ_l))²` for all `l`, `b_l ∈ B` and
`(α, γ_l) ∈ UAΓ_l`. The constant is the maximum over the locations taken on A3. -/
theorem lemma_A1_v (M : Model) (h1 : Assumption1 M) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ l, ∀ x ∈ UAΓ M l, ∀ b ∈ M.B,
      f M l b x.1 x.2 - f M l (bStarOf M l x.1 x.2) x.1 x.2 ≤
        K₀ * (b - bStarOf M l x.1 x.2) ^ 2 := by sorry

end MobilePromo
