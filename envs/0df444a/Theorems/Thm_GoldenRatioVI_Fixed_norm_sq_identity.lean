-- Prove2me | Theorems.Thm_GoldenRatioVI_Fixed_norm_sq_identity
-- name    : GoldenRatioVI.Fixed.norm_sq_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:56:59.291432+00:00
-- url     : https://prove2.me/theorems/b874f4a1-b4fc-4604-abb2-93be721e2b06
-- title:
--   Eq. (12) — golden-ratio identity for $\|z^{k+1}-z^*\|^2$
-- statement:
--   Let $\varphi=\frac{\sqrt5+1}2$ and let $(z^k)$, $(\bar z^k)$ be sequences in a real inner product space with $\bar z^k = \frac{(\varphi-1)z^k+\bar z^{k-1}}{\varphi}$ for every $k\ge1$. Then for every point $z^*$ and every $k\ge0$
--   $$\begin{aligned}
--   \|z^{k+1}-z^*\|^2 &= (1+\varphi)\|\bar z^{k+1}-z^*\|^2 - \varphi\|\bar z^k-z^*\|^2 + \varphi(1+\varphi)\|\bar z^{k+1}-\bar z^k\|^2\\
--   &= (1+\varphi)\|\bar z^{k+1}-z^*\|^2 - \varphi\|\bar z^k-z^*\|^2 + \frac1\varphi\|z^{k+1}-\bar z^k\|^2.
--   \end{aligned}$$
--
--   The identity converts the distance of the new iterate into distances of the averaged sequence $(\bar z^k)$; it is where the golden ratio enters the analysis of the algorithm.
--
--   **Formalization Note** Only the averaging step of (6) is assumed; no hypothesis on $F$, $g$ or $z^*$ is needed. The paper uses the identity for $k\ge1$ and $z^*\in S$; it holds for every $k\ge0$ and every $z^*$.
-- source:
--   Malitsky, Golden Ratio Algorithms for Variational Inequalities, preprint (Optimization Online 6598, 2018), p. 4, Eq. (12) (proof of Theorem 1)

import Mathlib
import Definitions.Def_GoldenRatioVI_Fixed_IsGRAALRun
open scoped goldenRatio

namespace GoldenRatioVI.Fixed

/-- Eq. (12): if `z̄ᵏ = ((φ - 1) zᵏ + z̄ᵏ⁻¹) / φ` for all `k ≥ 1`, then for every point `z*`
and every `k`,
`‖zᵏ⁺¹ - z*‖² = (1+φ)‖z̄ᵏ⁺¹ - z*‖² - φ‖z̄ᵏ - z*‖² + φ(1+φ)‖z̄ᵏ⁺¹ - z̄ᵏ‖²
             = (1+φ)‖z̄ᵏ⁺¹ - z*‖² - φ‖z̄ᵏ - z*‖² + (1/φ)‖zᵏ⁺¹ - z̄ᵏ‖²`. -/
theorem norm_sq_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z zbar : ℕ → E) (hbar : IsGoldenAveraging z zbar) (zs : E) (k : ℕ) :
    ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + φ * (1 + φ) * ‖zbar (k + 1) - zbar k‖ ^ 2 ∧
      ‖z (k + 1) - zs‖ ^ 2 =
        (1 + φ) * ‖zbar (k + 1) - zs‖ ^ 2 - φ * ‖zbar k - zs‖ ^ 2
          + (1 / φ) * ‖z (k + 1) - zbar k‖ ^ 2 := by sorry

end GoldenRatioVI.Fixed
