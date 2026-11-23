-- Prove2me | Theorems.Thm_OptInapprox_Bal2Sat_Supplement_theorem_7
-- name    : OptInapprox.Bal2Sat.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:00:06.545486+00:00
-- url     : https://prove2.me/theorems/c0e0f070-416b-4515-94c4-e6492f2795fd
-- title:
--   Theorem 7 — level-one Fourier weight is at most 4(U(µ)+ε)² for low-influence functions
-- statement:
--   Let $\varphi$ and $\Phi$ be the standard Gaussian density and distribution function and $U(x)=\varphi(\Phi^{-1}(x))$ the Gaussian isoperimetric function on $[0,1]$. There is an absolute constant $C>0$ such that, for every $f:\{-1,1\}^n\to[-1,1]$ with $\operatorname{Inf}_i(f)\le\delta$ for all $i$, setting $\mu=\frac12+\frac12\mathbb E[f]$,
--
--   $$\sum_{|S|=1}\hat f(S)^2\le4\,(U(\mu)+\epsilon)^2,\qquad \epsilon=\max\{1,\sqrt{|\Phi^{-1}(\mu)|}\}\cdot C\sqrt\delta.$$
--
--   Fourier coefficients and influences are the published Boolean ones. The result refines Theorem 6 in terms of the mean and approaches Talagrand's level-one bound as the mean becomes small.
--
--   Differences from the source:
--   - reading: ε = max{1,√|Φ⁻¹(µ)|}·O(√δ) → ε = max 1 √|Φ⁻¹ µ| · (C·√δ) with one absolute C>0 chosen before n, f and δ; reason: uniform reading of O(·)
--   - encoding: Φ⁻¹(µ) and U(µ) at µ∈{0,1} → Φ⁻¹ placeholder 0 and U = 0; reason: µ∈{0,1} forces f constant, so the level-one weight is 0 and the inequality holds whatever the boundary values
--   - encoding: Inf_i(f) ≤ δ for all i → same, for every real δ; reason: direct transcription with the published influence
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 13, Theorem 7; proof §10, pp. 25–26

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Supplement_Threshold

namespace OptInapprox.Bal2Sat.Supplement

theorem theorem_7 : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ), (∀ x, -1 ≤ f x ∧ f x ≤ 1) →
      ∀ δ : ℝ, (∀ i, OptInapprox.MaxCut.influence i f ≤ δ) →
        let μ : ℝ := 1 / 2 + 1 / 2 * OptInapprox.MaxCut.cubeE f
        let ε : ℝ := max 1 (Real.sqrt |gaussCdfInv μ|) * (C * Real.sqrt δ)
        ∑ i : Fin n, OptInapprox.MaxCut.fourier f {i} ^ 2 ≤ 4 * (gaussIso μ + ε) ^ 2 := by sorry

end OptInapprox.Bal2Sat.Supplement
