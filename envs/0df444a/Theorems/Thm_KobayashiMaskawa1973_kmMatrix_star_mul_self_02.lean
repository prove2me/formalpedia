-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_02
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_02
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:58:42.389424+00:00
-- url     : https://prove2.me/theorems/be028b10-d752-4dc7-a888-641de0ba599d
-- title:
--   (0,2) entry of K dagger K vanishes
-- statement:
--   The (0, 2) entry of $K^\dagger K$ vanishes identically.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_02 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 0 2 = 0 := by sorry

end KobayashiMaskawa1973
