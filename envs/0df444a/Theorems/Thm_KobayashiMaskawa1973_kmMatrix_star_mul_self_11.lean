-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_11
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_11
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:46:40.461603+00:00
-- url     : https://prove2.me/theorems/a3b64783-0711-432c-8bb8-19b8ea2afb77
-- title:
--   (1,1) entry of K dagger K equals 1
-- statement:
--   For all parameters $\theta_1, \theta_2, \theta_3, \delta \in \mathbb{R}$, the $(1, 1)$ entry of $K^\dagger K$ equals 1:
--
--   $$(K^\dagger K)_{11} = |K_{01}|^2 + |K_{11}|^2 + |K_{21}|^2 = 1.$$
--
--   This follows from expanding the squared magnitudes of the second column entries and using $\cos^2 + \sin^2 = 1$ and $|e^{i\delta}| = 1$.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_11 (θ₁ θ₂ θ₃ δ : ℝ) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) 1 1 = 1 := by sorry

end KobayashiMaskawa1973
