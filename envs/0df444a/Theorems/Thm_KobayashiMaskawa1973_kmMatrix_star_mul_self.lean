-- Prove2me | Theorems.Thm_KobayashiMaskawa1973_kmMatrix_star_mul_self
-- name    : KobayashiMaskawa1973.kmMatrix_star_mul_self
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-09-24T18:17:01.290025+00:00
-- url     : https://prove2.me/theorems/908a51c9-1cdf-41f6-b036-c21673a6ec29
-- title:
--   Conjugate transpose times KM matrix is identity
-- statement:
--   For all real mixing angles $\theta_1, \theta_2, \theta_3 \in \mathbb{R}$ and phase $\delta \in \mathbb{R}$, the conjugate transpose $K^\dagger = \operatorname{star}(K)$ of the Kobayashi--Maskawa mixing matrix is its left inverse:
--
--   $$K(\theta_1, \theta_2, \theta_3, \delta)^\dagger K(\theta_1, \theta_2, \theta_3, \delta) = I.$$
--
--   This explicit matrix product calculation verifies that the columns of the Kobayashi--Maskawa matrix form an orthonormal basis of $\mathbb{C}^3$ for all parameters.
-- source:
--   M. Kobayashi and T. Maskawa, Progress of Theoretical Physics 49 (1973) 652-657, pp. 657, Eq. (13)

import Mathlib
import Definitions.Def_KobayashiMaskawa1973_Defs

open Matrix

namespace KobayashiMaskawa1973

theorem kmMatrix_star_mul_self (θ₁ θ₂ θ₃ δ : ℝ) :
    star (kmMatrix θ₁ θ₂ θ₃ δ) * kmMatrix θ₁ θ₂ θ₃ δ = 1 := by sorry

end KobayashiMaskawa1973
