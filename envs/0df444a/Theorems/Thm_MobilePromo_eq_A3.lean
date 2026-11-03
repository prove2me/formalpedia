-- Prove2me | Theorems.Thm_MobilePromo_eq_A3
-- name    : MobilePromo.eq_A3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:08.00735+00:00
-- url     : https://prove2.me/theorems/fcb4efd8-172c-4c83-a15b-ea677ac19b2b
-- title:
--   Inequality (A-3): $b^*_l$ is Lipschitz on $\mathcal{U}_{A\Gamma_l}$
-- statement:
--   Under Assumption 1, for each location $l$ there is $K_8^l>0$ such that for all $(\alpha,\gamma_l),(\hat\alpha,\hat\gamma_l)\in\mathcal U_{A\Gamma_l}$,
--
--   $$
--   |b_l^*(\alpha,\gamma_l)-b_l^*(\hat\alpha,\hat\gamma_l)|\le K_8^l\bigl(|\alpha-\hat\alpha|+\|\gamma_l-\hat\gamma_l\|\bigr).
--   $$
--
--   This transfers an error in the marginal value and in the parameter to the optimal bid, and is the first half of Lemma 1.
--
--   Differences from the source:
--   - encoding: the standing facts are left implicit: at least one location, $q_l>0$, $\sum_l q_l\le 1$, a true parameter in $\Gamma^{(0)}$ → `Model` has the fields `L_pos`, `q_pos`, `q_sum_le`, `Γ₀_nonempty`; reason: they only exclude undefined cases: $\hat K$ divides by $q_l$ (p.19), at most one impression arrives per period (p.7), and $\gamma^{(0)}\in\Gamma^{(0)}$ (p.8)
-- source:
--   Feng, Dawande, Janakiraman & Qi, An Asymptotically Tight Learning Algorithm for Mobile-Promotion Platforms, SSRN 3523491, (A-3), A5 (PDF 39)

import Mathlib
import Definitions.Def_MobilePromo_Assumption1
import Definitions.Def_MobilePromo_V

set_option autoImplicit false

namespace MobilePromo

/-- Inequality (A-3) (SSRN 3523491, (A-3), A5, PDF 39): `b*_l` is Lipschitz on `UAΓ_l`, that is,
`|b*_l(α, γ_l) - b*_l(α̂, γ̂_l)| ≤ K₈ˡ (|α - α̂| + ‖γ_l - γ̂_l‖)` with `K₈ˡ > 0` independent of the points. -/
theorem eq_A3 (M : Model) (h1 : Assumption1 M) (l : Fin M.L) :
    ∃ K₈ : ℝ, 0 < K₈ ∧ ∀ x ∈ UAΓ M l, ∀ y ∈ UAΓ M l,
      |bStarOf M l x.1 x.2 - bStarOf M l y.1 y.2| ≤ K₈ * (|x.1 - y.1| + ‖x.2 - y.2‖) := by sorry

end MobilePromo
