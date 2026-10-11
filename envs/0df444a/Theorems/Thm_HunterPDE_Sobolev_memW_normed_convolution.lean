-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_memW_normed_convolution
-- name    : HunterPDE.Sobolev.memW_normed_convolution
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T22:36:54.714982+00:00
-- url     : https://prove2.me/theorems/4a47e72f-0e45-4467-81d2-af8157bd3226
-- title:
--   Normalized bump convolution preserves weak Sobolev membership
-- statement:
--   For every nonnegative derivative order $k$, every $1\le p<\infty$, every normalized smooth bump $\rho$ centered at zero, and every $f\in W^{k,p}(\mathbb R^n)$,
--
--   $$\rho*f\in W^{k,p}(\mathbb R^n).$$
--
--   This is the Sobolev membership assertion for mollification in Theorem 3.19 and the first paragraph of the proof of Theorem 3.24. It is independent of any limit of bump radii.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 1.28 (printed pp. 12–13), Theorem 3.19 (printed p. 55), and proof of Theorem 3.24 (printed p. 59). Normalized shrinking smooth bumps implement the same approximate identity argument.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
open MeasureTheory Filter ContinuousLinearMap
open HunterPDE.Sobolev
open scoped Convolution Topology

theorem HunterPDE.Sobolev.memW_normed_convolution {n k : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f) :
    MemW k p Set.univ (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f) := by sorry
