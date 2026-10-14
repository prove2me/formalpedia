-- Prove2me | Theorems.Thm_MeasureTheory_eLpNorm_convolution_le_of_nonneg_normalized
-- name    : MeasureTheory.eLpNorm_convolution_le_of_nonneg_normalized
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T22:58:31.298429+00:00
-- url     : https://prove2.me/theorems/be569d3f-b16b-4b19-8f28-ebccb1a76a43
-- title:
--   Normalized nonnegative compact kernels contract finite Lp norms
-- statement:
--   Let $1\le p<\infty$, let $d\in L^p(\mathbb R^n)$, and let $\rho:\mathbb R^n\to\mathbb R$ be continuous with compact support, nonnegative everywhere, and satisfy $\int\rho=1$. Then
--
--   $$\|\rho*d\|_{L^p}\le\|d\|_{L^p}.$$
--
--   This is the normalized-kernel case of Young's convolution inequality. It gives uniform Lp control of mollified functions and their convolved weak derivative representatives, without smoothness or shrinking-support assumptions. Dimension zero and p=1 are included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 1.28 (printed pp. 12–13); the arbitrary normalized nonnegative continuous compact kernel formulation follows from the same Minkowski averaging bound.

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Theorems.Thm_MeasureTheory_eLpNorm_integral_le_lintegral

open MeasureTheory ContinuousLinearMap
open scoped Convolution

theorem MeasureTheory.eLpNorm_convolution_le_of_nonneg_normalized {n : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y = 1)
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume) :
    eLpNorm (ρ ⋆[lsmul ℝ ℝ, volume] d) p volume ≤ eLpNorm d p volume  := by sorry
