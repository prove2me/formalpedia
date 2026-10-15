-- Prove2me | Theorems.Thm_GDPRPrivacy_PriceRise_alpha1_le_alpha2
-- name    : GDPRPrivacy.PriceRise.alpha1_le_alpha2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-13T23:29:21.000192+00:00
-- url     : https://prove2.me/theorems/db2bb6c7-94f7-4e1b-8916-9f6902e9b10d
-- title:
--   p. 14 — α₁(x) ≤ α₂(x) for all x ∈ (0, 1)
-- statement:
--   For every opt-in benefit $0 < x < 1$,
--   $$\alpha_1(x) = \max\Big\{\frac{1 - 2x}{2}, 0\Big\} \;\le\; \alpha_2(x) = \max\Big\{\frac{2 - 4x + x^2}{2x}, 0\Big\}.$$
--
--   The pre-GDPR threshold separating cases 1a and 1b never exceeds the post-GDPR threshold separating cases 2a and 2b. Hence a case 1a equilibrium before the GDPR never coexists with a case 2b equilibrium after it, which leaves exactly three possible pairs of equilibria (Lemma A3).
-- source:
--   Choe, Matsushima & Shekhar, The Bright Side of the GDPR, ISER DP No. 1246 (June 2024), p. 14 ("one can verify that α₁(x) ≤ α₂(x) for all x ∈ (0, 1)"); restated p. 33

import Mathlib
import Definitions.Def_GDPRPrivacy_PriceRise_Model

namespace GDPRPrivacy.PriceRise

theorem alpha1_le_alpha2 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    alpha1 x ≤ alpha2 x := by sorry

end GDPRPrivacy.PriceRise
