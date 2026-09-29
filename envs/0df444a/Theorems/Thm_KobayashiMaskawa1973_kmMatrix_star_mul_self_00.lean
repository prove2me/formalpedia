-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_00
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_00
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:46:54.310768+00:00
-- url     : https://prove2.me/theorems/f2336f46-3e35-4370-8d77-8fb9d123f013
-- title:
--   (0,0) entry of K dagger K equals 1
-- statement:
--   For all parameters $\theta_1, \theta_2, \theta_3, \delta \in \mathbb{R}$, the $(0, 0)$ entry of $K^\dagger K$ equals 1:
--
--   $$(K^\dagger K)_{00} = |K_{00}|^2 + |K_{10}|^2 + |K_{20}|^2 = c_1^2 + s_1^2 c_2^2 + s_1^2 s_2^2 = c_1^2 + s_1^2(c_2^2 + s_2^2) = c_1^2 + s_1^2 = 1.$$
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_00 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 0 0 = 1 := by sorry

end KobayashiMaskawa1973
