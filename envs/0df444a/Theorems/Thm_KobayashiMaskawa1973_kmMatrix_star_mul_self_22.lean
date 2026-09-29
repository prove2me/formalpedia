-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_22
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_22
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:47:03.62899+00:00
-- url     : https://prove2.me/theorems/97a9bef3-483c-4937-bce1-f6358f61207b
-- title:
--   (2,2) entry of K dagger K equals 1
-- statement:
--   For all parameters $\theta_1, \theta_2, \theta_3, \delta \in \mathbb{R}$, the $(2, 2)$ entry of $K^\dagger K$ equals 1:
--
--   $$(K^\dagger K)_{22} = |K_{02}|^2 + |K_{12}|^2 + |K_{22}|^2 = 1.$$
--
--   This follows similarly from the normalization of the third column.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_22 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 2 2 = 1 := by sorry

end KobayashiMaskawa1973
