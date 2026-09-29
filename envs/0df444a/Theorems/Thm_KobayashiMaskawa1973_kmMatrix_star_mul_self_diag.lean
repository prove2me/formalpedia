-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_diag
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_diag
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:43:06.535271+00:00
-- url     : https://prove2.me/theorems/c8c286b3-7d09-4b8b-aa2b-3fdef9d494f3
-- title:
--   Diagonal entries of K dagger K equal 1
-- statement:
--   For all parameters $\theta_1, \theta_2, \theta_3, \delta \in \mathbb{R}$ and every coordinate $i \in \mathrm{Fin}\ 3$, the $i$-th diagonal entry of the matrix product $K^\dagger K$ equals 1:
--
--   $$(K(\theta_1, \theta_2, \theta_3, \delta)^\dagger K(\theta_1, \theta_2, \theta_3, \delta))_{ii} = 1.$$
--
--   This asserts the unit normalization $\|K_{*i}\|^2 = 1$ of each column of the Kobayashi--Maskawa mixing matrix.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_diag (θ₁ θ₂ θ₃ δ : ℝ) (i : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i i = 1 := by sorry

end KobayashiMaskawa1973
