-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_zeroExtension_of_bounded_trace_eq_zero
-- name    : HunterPDE.Shared.HasWeakDeriv.zeroExtension_of_bounded_trace_eq_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T20:49:46.784523+00:00
-- url     : https://prove2.me/theorems/a7f63a52-fe16-46a1-89c1-20a162501bc6
-- title:
--   Zero trace permits extension of weak first derivatives by zero
-- statement:
--   Let $1\le p<\infty$ and let $T$ be any bounded trace on the upper half-space, linear up to almost-everywhere equality and equal to boundary restriction on smooth functions compactly supported in the closed half-space. Suppose $f\in W^{1,p}$ and $Tf=0$ almost everywhere. For every multi-index $\alpha$ of order at most one and every weak derivative $g=\partial^\alpha f$ belonging to $L^p$ on the half-space, the zero extensions satisfy
--
--   $$\partial^\alpha(\mathbf 1_{\{x_n>0\}}f)=\mathbf 1_{\{x_n>0\}}g$$
--
--   weakly on the whole Euclidean space. The order-zero case is included. This isolates the absence of a boundary distribution in zero extension; it makes no approximation or trace-kernel characterization assumption.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73. Analytic zero-extension step of the converse outlined on printed p. 73; the source omits its proof.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.zeroExtension_of_bounded_trace_eq_zero {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0) (T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin m) → ℝ)
    (hlinear : (∀ f g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ,
        MemW 1 p (upperHalfSpace m) f → MemW 1 p (upperHalfSpace m) g → ∀ a b : ℝ,
          T (a • f + b • g) =ᵐ[volume] a • T f + b • T g))
    (hbound : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, MemW 1 p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧
          eLpNorm (T f) p volume ≤ (C : ℝ≥0∞) * sobolevNorm 1 p (upperHalfSpace m) f))
    (hsmooth : (∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, IsSmoothCompactClosedHalfSpace f →
        T f =ᵐ[volume] fun x' => f (boundaryPoint x')))
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW 1 p (upperHalfSpace m) f)
    (hzero : T f =ᵐ[volume] 0)
    (α : Fin (m + 1) → ℕ) (hα : ∑ i, α i ≤ 1)
    (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : HunterPDE.Shared.HasWeakDeriv (upperHalfSpace m) α f g)
    (hgp : MemLp g p (volume.restrict (upperHalfSpace m))) :
    HunterPDE.Shared.HasWeakDeriv Set.univ α
      ((upperHalfSpace m).indicator f) ((upperHalfSpace m).indicator g) := by sorry
