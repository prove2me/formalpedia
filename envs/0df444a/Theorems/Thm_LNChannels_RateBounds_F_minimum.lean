-- Prove2me | Theorems.Thm_LNChannels_RateBounds_F_minimum
-- name    : LNChannels.RateBounds.F_minimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:19.896354+00:00
-- url     : https://prove2.me/theorems/015ba59e-b62d-4792-9357-e9f69d6ef7d7
-- title:
--   Proof of Theorem 2(i), p. 11 — $F$ is convex, blows up at $0$ and $\infty$, and has the unique minimizer $\hat m=\cosh^{-1}(B\kappa/2+1)/\kappa$
-- statement:
--   Let $B>0$, $\kappa>0$ and $C\in\mathbb R$, and consider on $(0,\infty)$
--   $$F(m)=\frac{C}{1-e^{\kappa}}+\frac{B}{e^{\kappa m}-1}+m .$$
--   Then:
--   1. $F$ is convex on $(0,\infty)$;
--   2. $F(m)\to+\infty$ as $m\downarrow0$ and as $m\to\infty$;
--   3. $\hat m=\cosh^{-1}(B\kappa/2+1)/\kappa$ is positive and is the unique minimizer of $F$ on $(0,\infty)$: $F(\hat m)<F(m)$ for every $m>0$, $m\neq\hat m$;
--   4. $F'(\hat m)=0$, which reads $\dfrac{B\kappa}{2-2\cosh(\kappa\hat m)}+1=0$;
--   5. the minimum value is
--   $$F(\hat m)=\frac{C}{1-e^{\kappa}}+\frac{2B}{B\kappa+\sqrt{B\kappa(B\kappa+4)}}+\frac{\cosh^{-1}(B\kappa/2+1)}{\kappa}.$$
--
--   With $\kappa=\log(1+r/\lambda)$ this is the minimal excess of a unidirectional channel's cost over on-chain settlement, so a unidirectional channel is worthwhile exactly when $F(\hat m)<0$.
--
--   **Formalization Note** $\cosh^{-1}$ is Mathlib's `Real.arcosh`, $\log(x+\sqrt{x^2-1})$, evaluated at $B\kappa/2+1>1$. The statement holds for every $\kappa>0$, not only for $\kappa=\log(1+r/\lambda)$.
-- source:
--   Guasoni, Huberman & Shikhelman, Lightning Network Economics: Channels, Management Science (Articles in Advance, Nov. 6, 2023), DOI 10.1287/mnsc.2022.01664, p. 11 (PDF p. 12), proof of Theorem 2(i), displays for m̂ and F(m̂)

import Mathlib
import Definitions.Def_LNChannels_RateBounds_ClosedForms

namespace LNChannels.RateBounds

/-- Proof of Theorem 2(i), p. 11: for `B, κ > 0` the function
`F(m) = C/(1 − e^κ) + B/(e^{κm} − 1) + m` is convex on `(0, ∞)`, tends to `+∞` at `0⁺` and at `+∞`,
has the unique minimizer `m̂ = cosh⁻¹(Bκ/2 + 1)/κ` on `(0, ∞)`, which satisfies the first-order
condition `Bκ/(2 − 2 cosh(κ m̂)) + 1 = 0`, and
`F(m̂) = C/(1 − e^κ) + 2B/(Bκ + √(Bκ(Bκ + 4))) + cosh⁻¹(Bκ/2 + 1)/κ`. -/
theorem F_minimum (B κ C : ℝ) (hB : 0 < B) (hκ : 0 < κ) :
    let F : ℝ → ℝ := fun m => C / (1 - Real.exp κ) + B / (Real.exp (κ * m) - 1) + m
    let mhat := Real.arcosh (B * κ / 2 + 1) / κ
    ConvexOn ℝ (Set.Ioi 0) F ∧
      Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop ∧
      Filter.Tendsto F Filter.atTop Filter.atTop ∧
      0 < mhat ∧
      (∀ m : ℝ, 0 < m → m ≠ mhat → F mhat < F m) ∧
      HasDerivAt F 0 mhat ∧
      B * κ / (2 - 2 * Real.cosh (κ * mhat)) + 1 = 0 ∧
      F mhat = C / (1 - Real.exp κ) + 2 * B / (B * κ + √(B * κ * (B * κ + 4)))
        + Real.arcosh (B * κ / 2 + 1) / κ := by sorry

end LNChannels.RateBounds
