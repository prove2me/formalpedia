-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_single_section_ordinary_localization_charts
-- name    : MazurTransfer.order13_actual_single_section_ordinary_localization_charts
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T04:03:27.971341+00:00
-- url     : https://prove2.me/theorems/38e843a2-1279-460d-92a8-8581dbacb4bb
-- title:
--   Actual single-section coordinate algebra: two ordinary localization isomorphisms and exact principal-open covers
-- statement:
--   Let $R$ be any commutative ring and set
--
--   $$A_R=R[x,y]/(y^2-(x^6+2x^5+x^4+2x^3+6x^2+4x+1)).$$
--
--   Put $t=y+x^3+x^2+1$, $p=xt$ and $q=x(p+2)$. Give $A_R$ its actual $R[T]$-algebra structure by $T\mapsto t$, and let $B_R=R[T][p,q]\subseteq A_R$. The actual inclusion induces coefficient-preserving algebra isomorphisms
--
--   $$B_R[1/t]\simeq A_R[1/t],\qquad B_R[1/(p+2)]\simeq A_R[1/(p+2)].$$
--
--   Each isomorphism sends every original element of $B_R$ to its image under the inclusion. If $2$ is a unit in $R$, the actual principal opens satisfy
--
--   $$D_A(t)\cup D_A(p+2)=\operatorname{Spec}A_R,$$
--
--   $$D_B(t)\cup D_B(p+2)\cup D_B(p(p+t))=\operatorname{Spec}B_R.$$
--
--   No field, domain, noetherianity, supplied basis, supplied localization isomorphism or scheme-complement identification is assumed. These results supply the ordinary-chart comparisons for the finite map adapted to one infinity section. The reciprocal-chart comparison, identification of $\operatorname{Spec}B_R$ with the curve minus that section, full finite-map data, integral Picard representation and rational rank zero remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned actual coordinate-ring, localization, inverse and unit-ideal arguments using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve

theorem MazurTransfer.order13_actual_single_section_ordinary_localization_charts.{u}
    (R : Type u) [CommRing R] :
    let τ : CoordinateRing R := yCoordinate R + (xCoordinate R ^ 3 + xCoordinate R ^ 2 + 1)
    let μ : CoordinateRing R := xCoordinate R * τ
    let ν : CoordinateRing R := xCoordinate R * (μ + 2)
    let α : Algebra (Polynomial R) (CoordinateRing R) := (aeval τ).toRingHom.toAlgebra
    letI : Algebra (Polynomial R) (CoordinateRing R) := α
    letI : SMul (Polynomial R) (CoordinateRing R) := α.toSMul
    letI : Module (Polynomial R) (CoordinateRing R) :=
      @Algebra.toModule (Polynomial R) (CoordinateRing R) _ _ α
    let B : Subalgebra (Polynomial R) (CoordinateRing R) :=
      Algebra.adjoin (Polynomial R) ({μ,ν} : Set (CoordinateRing R))
    let β : Algebra R B := ((algebraMap (Polynomial R) B).comp Polynomial.C).toAlgebra
    letI : Algebra R B := β
    ∃ tB pB qB : B,
      (tB : CoordinateRing R) = τ ∧ (pB : CoordinateRing R) = μ ∧
      (qB : CoordinateRing R) = ν ∧
      ∃ eτ : Localization.Away tB ≃ₐ[R] Localization.Away τ,
      ∃ eκ : Localization.Away (pB + 2) ≃ₐ[R] Localization.Away (μ + 2),
      (∀ b : B, eτ (algebraMap B (Localization.Away tB) b) =
        algebraMap (CoordinateRing R) (Localization.Away τ) (b : CoordinateRing R)) ∧
      (∀ b : B, eκ (algebraMap B (Localization.Away (pB + 2)) b) =
        algebraMap (CoordinateRing R) (Localization.Away (μ + 2)) (b : CoordinateRing R)) ∧
      (IsUnit (2 : R) →
        PrimeSpectrum.basicOpen τ ⊔ PrimeSpectrum.basicOpen (μ + 2) = ⊤ ∧
        PrimeSpectrum.basicOpen tB ⊔ (PrimeSpectrum.basicOpen (pB + 2) ⊔
          PrimeSpectrum.basicOpen (pB * (pB + tB))) = ⊤) := by sorry
