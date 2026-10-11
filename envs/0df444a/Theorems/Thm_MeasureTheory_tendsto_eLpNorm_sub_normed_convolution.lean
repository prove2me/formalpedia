-- Prove2me | Theorems.Thm_MeasureTheory_tendsto_eLpNorm_sub_normed_convolution
-- name    : MeasureTheory.tendsto_eLpNorm_sub_normed_convolution
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T22:39:41.284948+00:00
-- url     : https://prove2.me/theorems/d1892d7f-352a-4460-a5cf-6dd506f365f3
-- title:
--   Normalized shrinking bump convolutions converge in finite Lp
-- statement:
--   Let $1\le p<\infty$ and $d\in L^p(\mathbb R^n)$. If $\rho_m$ are smooth nonnegative normalized bumps centered at zero whose support radii tend to zero, then
--
--   $$\|d-\rho_m*d\|_{L^p}\longrightarrow0.$$
--
--   This is the approximate identity convergence underlying Hunter Theorem 1.28 and the proof of Theorem 3.24. No Sobolev membership or derivative assumptions are needed. Dimension zero is included.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 1.28 (printed pp. 12–13), Theorem 3.19 (printed p. 55), and proof of Theorem 3.24 (printed p. 59). Normalized shrinking smooth bumps implement the same approximate identity argument.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
open MeasureTheory Filter ContinuousLinearMap
open HunterPDE.Sobolev
open scoped Convolution Topology

theorem MeasureTheory.tendsto_eLpNorm_sub_normed_convolution {n : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (d : EuclideanSpace ℝ (Fin n) → ℝ) (hd : MemLp d p volume) :
    Tendsto (fun m => eLpNorm (d - ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] d)) p volume)
      atTop (𝓝 0) := by sorry
