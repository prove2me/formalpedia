-- Prove2me | Theorems.Thm_HunterPDE_Shared_integral_mul_smooth_normal
-- name    : HunterPDE.Shared.integral_mul_smooth_normal
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:02:11.840808+00:00
-- url     : https://prove2.me/theorems/e9198782-cac5-4003-ba29-31556ec2a1cc
-- title:
--   Smooth half-space normal Green identity
-- statement:
--   For smooth compactly supported $f,\psi$ on $\mathbb R^{m+1}$,
--   $$\int_{\mathbb R^{m+1}_+}\partial_{m+1}f\,\psi=-\int_{\mathbb R^{m+1}_+}f\,\partial_{m+1}\psi-\int_{\mathbb R^m}f(x',0)\psi(x',0)\,dx'.$$
--   This includes $m=0$ and retains the nonzero boundary contribution. One-dimensional integration by parts on normal rays and Fubini prove it. It is the classical ingredient in extending Green's formula by Sobolev density.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorems 3.42 and 3.44, printed pp. 72–73. Auxiliary ingredient for the normal Green identity, not an explicit numbered theorem in the source.

import Definitions.Def_HunterPDE_Compactness_HalfSpace
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory HunterPDE.Compactness HunterPDE.Shared Filter
open scoped ENNReal Topology ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.integral_mul_smooth_normal {m : ℕ}
    (f ψ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
    (hf : IsTestFunction Set.univ f) (hψ : IsTestFunction Set.univ ψ) :
    (∫ x in upperHalfSpace m, partialDeriv f (Fin.last m) x * ψ x) =
      -(∫ x in upperHalfSpace m, f x * multiDeriv ψ (Pi.single (Fin.last m) 1) x) -
        ∫ x', f (boundaryPoint x') * ψ (boundaryPoint x') := by sorry
