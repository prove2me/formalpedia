-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_single_section_reciprocal_localization_isomorphism
-- name    : MazurTransfer.order13_actual_single_section_reciprocal_localization_isomorphism
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T04:41:36.414978+00:00
-- url     : https://prove2.me/theorems/a5362e02-8efa-40f5-81c5-365e9533dab4
-- title:
--   Actual single-section reciprocal localization isomorphism over integral bases
-- statement:
--   Let $R$ be a noetherian integral domain in which $104$ is a unit. Set
--
--   $$A_R=R[x,y]/(y^2-(x^6+2x^5+x^4+2x^3+6x^2+4x+1)).$$
--
--   Put $t=y+x^3+x^2+1$, $p=xt$, $q=x(p+2)$ and $B_R=R[T][p,q]\subseteq A_R$, with the actual parameter action $T\mapsto t$. Let
--
--   $$C_R=R[z,w]/(w^2-(z^6+4z^5+6z^4+2z^3+z^2+2z+1)),$$
--
--   $$d=w-1-z-z^3,\qquad d'=w-1-z+z^3,\qquad P_R=C_R[1/(dd')].$$
--
--   The following elements are regular in $P_R$:
--
--   $$t_P=\frac{4z(1+z)}d,\qquad p_P=\frac{4(1+z)}d,\qquad q_P=\frac{8z^2(1+z)^2}{dd'}.$$
--
--   There exists a coefficient-preserving algebra isomorphism
--
--   $$\chi:P_R\simeq B_R[1/(p(p+t))]$$
--
--   sending $t_P,p_P,q_P$ to the images of the actual $t,p,q$. The domain, noetherianity and invertibility hypotheses are explicit; no field, supplied map, supplied basis or supplied curve-complement hypothesis is assumed. This is an actual reciprocal-chart comparison map. The exact complement of the positive infinity section, full finite-map data, compatible integral Picard representation and rational rank zero remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned recovered reciprocal-coordinate, unit, universal-property and surjectivity proofs using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained. The unchanged public actual-curve geometric-integrality and flatness/smoothness results supply the coordinate-domain proofs; the actual overlap equivalence and faithful localizations prove injectivity.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_single_section_reciprocal_localization_isomorphism.{u}
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
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
    let d : ReciprocalRing R := wCoordinate R - 1 - zCoordinate R - zCoordinate R ^ 3
    let d' : ReciprocalRing R := wCoordinate R - 1 - zCoordinate R + zCoordinate R ^ 3
    let P := Localization.Away (d * d')
    let zP : P := algebraMap (ReciprocalRing R) P (zCoordinate R)
    let di : P := algebraMap (ReciprocalRing R) P d' * IsLocalization.Away.invSelf (d * d')
    let d'i : P := algebraMap (ReciprocalRing R) P d * IsLocalization.Away.invSelf (d * d')
    let τP : P := 4 * zP * (1 + zP) * di
    let μP : P := 4 * (1 + zP) * di
    let νP : P := 8 * zP ^ 2 * (1 + zP) ^ 2 * di * d'i
    ∃ tB pB qB : B,
      (tB : CoordinateRing R) = τ ∧ (pB : CoordinateRing R) = μ ∧
      (qB : CoordinateRing R) = ν ∧
      ∃ χ : P ≃ₐ[R] Localization.Away (pB * (pB + tB)),
        χ τP = algebraMap B (Localization.Away (pB * (pB + tB))) tB ∧
        χ μP = algebraMap B (Localization.Away (pB * (pB + tB))) pB ∧
        χ νP = algebraMap B (Localization.Away (pB * (pB + tB))) qB := by sorry
