-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_bounded_trace_normal
-- name    : HunterPDE.Shared.HasWeakDeriv.integral_mul_bounded_trace_normal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T17:13:07.092748+00:00
-- url     : https://prove2.me/theorems/1adb2ba1-d1e5-4e7e-a708-b1459e86d2d7
-- title:
--   Normal Green identity for any bounded half-space trace
-- statement:
--   Let $1\le p<\infty$ and let $T:W^{1,p}(\mathbb R^{m+1}_+)\to L^p(\mathbb R^m)$ be a trace map, linear up to almost-everywhere equality, bounded by a finite constant, and agreeing with boundary restriction on smooth functions compactly supported in the closed half-space. For $f\in W^{1,p}$, let $g=\partial_{m+1}f\in L^p$ be any representative of its normal weak derivative. For every whole-space smooth compactly supported test function $\psi$,
--   $$\int_{\mathbb R^{m+1}_+}g\psi=-\int_{\mathbb R^{m+1}_+}f\,\partial_{m+1}\psi-\int_{\mathbb R^m}(Tf)(x')\psi(x',0)\,dx'.$$
--   The boundary term has a minus sign because the outward normal is $-e_{m+1}$. No zero-trace hypothesis is imposed. The statement includes $p=1$ and $m=0$. This Green identity isolates the boundary contribution to the distributional derivative of a zero extension.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.44, printed pp. 72–73. Analytic zero-extension step of the converse outlined on printed p. 73; the source omits its proof. General Green identity underlying this step, obtained by smooth half-space approximation (Theorem 3.42) and continuity of the bounded trace. The identity is an auxiliary consequence, not an explicit statement in Hunter.

import Definitions.Def_HunterPDE_Compactness_Sobolev
import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.integral_mul_bounded_trace_normal {m : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
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
    (g : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hg : HunterPDE.Shared.HasWeakDeriv (upperHalfSpace m) (Pi.single (Fin.last m) 1) f g)
    (hgp : MemLp g p (volume.restrict (upperHalfSpace m)))
    (ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hψ : HunterPDE.Shared.IsTestFunction Set.univ ψ) :
    (∫ x in upperHalfSpace m, g x * ψ x) =
      -(∫ x in upperHalfSpace m,
        f x * HunterPDE.Shared.multiDeriv ψ (Pi.single (Fin.last m) 1) x) -
      ∫ x', T f x' * ψ (boundaryPoint x') := by sorry
