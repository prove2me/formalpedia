-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_20
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_20
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:59:01.789499+00:00
-- url     : https://prove2.me/theorems/88b1dc00-bcaa-43e7-94dc-4077b9886bb9
-- title:
--   (2,0) entry of K dagger K vanishes
-- statement:
--   The (2, 0) entry of $K^\dagger K$ vanishes identically.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_20 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 2 0 = 0 := by sorry

end KobayashiMaskawa1973
