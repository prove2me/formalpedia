-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_offdiag
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_offdiag
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:43:00.833973+00:00
-- url     : https://prove2.me/theorems/a3702427-4903-4e09-b417-86f359ac702d
-- title:
--   Off-diagonal entries of K dagger K equal 0
-- statement:
--   For all parameters $\theta_1, \theta_2, \theta_3, \delta \in \mathbb{R}$ and distinct coordinates $i, j \in \mathrm{Fin}\ 3$ with $i \neq j$, the off-diagonal entry of the matrix product $K^\dagger K$ vanishes:
--
--   $$i \neq j \implies (K(\theta_1, \theta_2, \theta_3, \delta)^\dagger K(\theta_1, \theta_2, \theta_3, \delta))_{ij} = 0.$$
--
--   This asserts the pairwise orthogonality $\langle K_{*i}, K_{*j} \rangle = 0$ between distinct columns of the Kobayashi--Maskawa matrix.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_offdiag (θ₁ θ₂ θ₃ δ : ℝ) (i j : Fin 3) (h : i ≠ j) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i j = 0 := by sorry

end KobayashiMaskawa1973
