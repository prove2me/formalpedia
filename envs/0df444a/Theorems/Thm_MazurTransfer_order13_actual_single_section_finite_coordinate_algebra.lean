-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_single_section_finite_coordinate_algebra
-- name    : MazurTransfer.order13_actual_single_section_finite_coordinate_algebra
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T03:15:46.939901+00:00
-- url     : https://prove2.me/theorems/01fdedd6-1fb9-4206-b72b-005c1751e77a
-- title:
--   Actual single-section coordinate algebra is finite and spanned by three explicit generators
-- statement:
--   Let $R$ be a commutative ring in which $2$ is a unit, and let
--
--   $$A_R=R[x,y]/(y^2-(x^6+2x^5+x^4+2x^3+6x^2+4x+1)).$$
--
--   Set $t=y+x^3+x^2+1$, $p=xt$, and $q=x(p+2)$, and give $A_R$ its actual $R[T]$-algebra structure by $T\mapsto t$. The actual subalgebra $B_R=R[T][p,q]\subseteq A_R$ satisfies
--
--   $$B_R=R[T]\cdot 1+R[T]\cdot p+R[T]\cdot q.$$
--
--   In particular, $B_R$ is finite as an $R[T]$-module. No field, domain, noetherianity, supplied algebra presentation, basis, affine-open identification or finiteness hypothesis is assumed. This is an algebraic input for a finite map adapted to the positive infinity section of the actual order-13 curve. Free rank three, identification of $\operatorname{Spec}B_R$ with the curve minus that section, full finite-map data, Picard representability and rational rank zero remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned coordinate-ring, span and finite-module arguments using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve

theorem MazurTransfer.order13_actual_single_section_finite_coordinate_algebra.{u}
    (R : Type u) [CommRing R] (h2 : IsUnit (2 : R)) :
    let τ : CoordinateRing R := yCoordinate R + (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1)
    let μ : CoordinateRing R := xCoordinate R * τ
    let ν : CoordinateRing R := xCoordinate R * (μ + 2)
    let α : Algebra (Polynomial R) (CoordinateRing R) := (aeval τ).toRingHom.toAlgebra
    letI : Algebra (Polynomial R) (CoordinateRing R) := α
    letI : SMul (Polynomial R) (CoordinateRing R) := α.toSMul
    letI : Module (Polynomial R) (CoordinateRing R) :=
      @Algebra.toModule (Polynomial R) (CoordinateRing R) _ _ α
    ∃ B : Subalgebra (Polynomial R) (CoordinateRing R),
      B = Algebra.adjoin (Polynomial R) ({μ, ν} : Set (CoordinateRing R)) ∧
      B.toSubmodule = Submodule.span (Polynomial R) ({1, μ, ν} : Set (CoordinateRing R)) ∧
      Module.Finite (Polynomial R) B := by sorry
