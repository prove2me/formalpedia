-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self_entries
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self_entries
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:29:11.155658+00:00
-- url     : https://prove2.me/theorems/3b821f74-5136-4df6-a88f-b78cfad2597c
-- title:
--   Every entry of K dagger times K matches identity
-- statement:
--   For all parameters $\theta_1, \theta_2, \theta_3, \delta \in \mathbb{R}$ and all matrix coordinates $i, j \in \mathrm{Fin}\ 3$, the $(i, j)$-entry of the product $K^\dagger K$ equals the Kronecker delta $\delta_{ij}$ (the $(i, j)$-entry of the identity matrix $I_3$):
--
--   $$(K^\dagger K)_{ij} = \delta_{ij}.$$
--
--   For $i = j$, the diagonal sums of squares of cosines and sines reduce to 1; for $i \neq j$, cross terms cancel to 0.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self_entries (θ₁ θ₂ θ₃ δ : ℝ) (i j : Fin 3) :
    (star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ) i j = (1 : Matrix (Fin 3) (Fin 3) ℂ) i j := by sorry

end KobayashiMaskawa1973
