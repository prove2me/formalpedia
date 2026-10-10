-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_inverse_parameter_localization_charts
-- name    : MazurTransfer.order13_actual_inverse_parameter_localization_charts
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T08:58:16.770435+00:00
-- url     : https://prove2.me/theorems/d50bcf04-0def-425c-9f0c-54e9cbcd9b39
-- title:
--   Actual inverse-parameter finite algebra and two localization charts
-- statement:
--   Let $R$ be a noetherian integral domain with $104$ invertible, and let
--   $$A=R[x,y]/(y^2-(x^6+2x^5+x^4+2x^3+6x^2+4x+1)).$$
--   Put $t=y+x^3+x^2+1$, $p=xt$, $q=x(p+2)$. In $A[1/t]$, put $s=1/t$, $a=p/t^2$, $b=q/t^2$, and form the literal subalgebra $B=R[S][a,b]$, with $S$ acting by $s$. This algebra is finite over $R[S]$. With $L=1-2s-2b$ and $H=L-4a^2$, its spectrum is covered by $D(s)$ and $D(HL)$.
--
--   Let $C=R[z,w]/(w^2-(z^6+4z^5+6z^4+2z^3+z^2+2z+1))$, $f=w+1+z+z^3$, $g=f+2z^4$, $P=C[1/(fg)]$, and $r=1/f$. There are coefficient-preserving isomorphisms
--   $$B[1/s]\simeq A[1/t],\qquad P\simeq B[1/(HL)].$$
--   The first retains the literal inclusion of every element of $B$. The second sends $z^3r,z^2r,zr+2z^5r^2$ to the images of $s,a,b$ respectively.
--
--   These are the two explicit affine charts of the inverse-parameter finite scheme. Their gluing into the original whole curve, complete finite-map data, integral Picard compatibility and rational rank zero remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned recovered reciprocal-coordinate, unit, universal-property and surjectivity proofs using Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Attribution retained. The unchanged public actual-curve geometric-integrality and flatness/smoothness results supply the coordinate-domain proofs; the actual overlap equivalence and faithful localizations prove injectivity. Complete owned inverse-parameter multiplication, finite-algebra, localization, regular reciprocal-coordinate and faithful comparison proofs; no original-source count increment.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth
import Definitions.Def_MazurTransfer_Order13InverseParameterCoordinates

open Polynomial
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13InverseParameterPublicCoordinates

theorem MazurTransfer.order13_actual_inverse_parameter_localization_charts.{u} (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    ∃ sB aB bB : MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R,
    (sB : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R) =
      MazurTransfer.Order13InverseParameterPublicCoordinates.s R ∧
    (aB : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R) =
      MazurTransfer.Order13InverseParameterPublicCoordinates.a R ∧
    (bB : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R) =
      MazurTransfer.Order13InverseParameterPublicCoordinates.b R ∧
    Module.Finite (Polynomial R) (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) ∧
    (PrimeSpectrum.basicOpen sB ⊔ PrimeSpectrum.basicOpen
      ((1 - 2 * sB - 2 * bB - 4 * aB ^ 2) * (1 - 2 * sB - 2 * bB)) = ⊤) ∧
    ∃ κ : Localization.Away sB ≃ₐ[R]
        MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R,
      (∀ v : MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R,
        κ (algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R)
          (Localization.Away sB) v) = (v : MazurTransfer.Order13InverseParameterPublicCoordinates.OrdinaryLocalization R)) ∧
      ∃ χ : MazurTransfer.Order13InverseParameterPublicCoordinates.PatchRing R ≃ₐ[R]
          Localization.Away ((1 - 2 * sB - 2 * bB - 4 * aB ^ 2) * (1 - 2 * sB - 2 * bB)),
        χ (MazurTransfer.Order13InverseParameterPublicCoordinates.patchS R) =
          algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) _ sB ∧
        χ (MazurTransfer.Order13InverseParameterPublicCoordinates.patchA R) =
          algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) _ aB ∧
        χ (MazurTransfer.Order13InverseParameterPublicCoordinates.patchB R) =
          algebraMap (MazurTransfer.Order13InverseParameterPublicCoordinates.candidateAlgebra R) _ bB
 := by sorry
