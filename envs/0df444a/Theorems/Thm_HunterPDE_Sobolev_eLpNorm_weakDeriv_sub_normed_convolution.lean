-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_eLpNorm_weakDeriv_sub_normed_convolution
-- name    : HunterPDE.Sobolev.eLpNorm_weakDeriv_sub_normed_convolution
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T22:37:36.388166+00:00
-- url     : https://prove2.me/theorems/ce156632-17b8-4a9d-bf7f-be69fa0ef265
-- title:
--   Weak derivative error norm under normalized bump convolution
-- statement:
--   Let $f\in W^{k,p}(\mathbb R^n)$, $1\le p<\infty$, let $d\in L^p$ represent a weak derivative $D^\alpha f$ with $|\alpha|\le k$, and let $\rho$ be a normalized smooth compactly supported bump. Then
--
--   $$\|D^\alpha(f-\rho*f)\|_{L^p}=\|d-\rho*d\|_{L^p}.$$
--
--   The left side uses any chosen weak derivative representative. The identity expresses convolution commutation, linearity, and almost everywhere uniqueness of weak derivatives, as used in Theorem 3.19 and the proof of Theorem 3.24. It permits arbitrary representatives of the input derivative.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 1.28 (printed pp. 12–13), Theorem 3.19 (printed p. 55), and proof of Theorem 3.24 (printed p. 59). Normalized shrinking smooth bumps implement the same approximate identity argument.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
open MeasureTheory Filter ContinuousLinearMap
open HunterPDE.Sobolev
open scoped Convolution Topology

theorem HunterPDE.Sobolev.eLpNorm_weakDeriv_sub_normed_convolution {n k : ℕ} {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : MemW k p Set.univ f)
    (α : Fin n → ℕ) (hα : ∑ i, α i ≤ k)
    (d : EuclideanSpace ℝ (Fin n) → ℝ)
    (hd : HasWeakDeriv Set.univ α f d) (hdp : MemLp d p volume) :
    eLpNorm (weakDeriv Set.univ α (f - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] f))) p volume =
      eLpNorm (d - (φ.normed volume ⋆[lsmul ℝ ℝ, volume] d)) p volume := by sorry
