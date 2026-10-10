-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_single_section_finite_coordinate_algebra_basis
-- name    : MazurTransfer.order13_actual_single_section_finite_coordinate_algebra_basis
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T03:37:28.558324+00:00
-- url     : https://prove2.me/theorems/ff3012ed-8c1d-4213-9a43-6d2c01b574d3
-- title:
--   Actual single-section coordinate algebra has the explicit free rank-three basis
-- statement:
--   Let $R$ be an integral domain in which $2$ is a unit, and let
--
--   $$A_R=R[x,y]/(y^2-(x^6+2x^5+x^4+2x^3+6x^2+4x+1)).$$
--
--   Set $t=y+x^3+x^2+1$, $p=xt$ and $q=x(p+2)$, and give $A_R$ its actual $R[T]$-algebra structure by $T\mapsto t$. The actual subalgebra $B_R=R[T][p,q]\subseteq A_R$ has the explicit basis
--
--   $$B_R=R[T]\cdot 1\oplus R[T]\cdot p\oplus R[T]\cdot q.$$
--
--   In particular it is finite free of rank three over $R[T]$. The basis is constructed with its three entries exactly $1,p,q$. No field, noetherianity, supplied basis, supplied algebra presentation, affine-open identification or rank hypothesis is assumed. This supplies the algebraic freeness input for a finite map adapted to the positive infinity section of the actual order-13 curve. Identification of $\operatorname{Spec}B_R$ with the curve minus that section, full finite-map data, integral Picard representability, torsion specialization and rational rank zero remain separate obligations
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned coordinate-ring, span and finite-module arguments using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve

theorem MazurTransfer.order13_actual_single_section_finite_coordinate_algebra_basis.{u}
    (R : Type u) [CommRing R] [IsDomain R] (h2 : IsUnit (2 : R)) :
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
      Module.Finite (Polynomial R) B ∧
      Module.Free (Polynomial R) B ∧ Module.finrank (Polynomial R) B = 3 ∧
      ∃ b : Module.Basis (Fin 3) (Polynomial R) B,
        (b 0 : CoordinateRing R) = 1 ∧ (b 1 : CoordinateRing R) = μ ∧
          (b 2 : CoordinateRing R) = ν := by sorry
