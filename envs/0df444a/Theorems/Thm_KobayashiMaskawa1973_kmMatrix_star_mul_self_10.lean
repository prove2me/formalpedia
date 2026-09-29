-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_10
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_10
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:58:52.819064+00:00
-- url     : https://prove2.me/theorems/e972d2cd-38eb-408a-8249-7743e06e4869
-- title:
--   (1,0) entry of K dagger K vanishes
-- statement:
--   The (1, 0) entry of $K^\dagger K$ vanishes identically.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_10 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 1 0 = 0 := by sorry

end KobayashiMaskawa1973
