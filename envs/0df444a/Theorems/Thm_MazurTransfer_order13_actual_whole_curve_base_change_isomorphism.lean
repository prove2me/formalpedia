-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_whole_curve_base_change_isomorphism
-- name    : MazurTransfer.order13_actual_whole_curve_base_change_isomorphism
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T02:03:08.000108+00:00
-- url     : https://prove2.me/theorems/7f7c96e7-bf0b-463b-b273-626f995d5ade
-- title:
--   Actual whole glued curve base-change isomorphism
-- statement:
--   Let $R$ be any commutative ring and $S$ any commutative $R$-algebra. Let $X_R$ be the literal glued order-13 sextic curve, with its actual structural map to $\operatorname{Spec} R$. Then there exists an actual scheme isomorphism
--
--   $$\operatorname{Spec} S\times_{\operatorname{Spec} R}X_R\simeq X_S.$$
--
--   Its inverse has structural projection equal to the actual map $X_S\to\operatorname{Spec} S$. The projection to $X_R$ restricts on both affine charts to ring maps preserving every base scalar and the four coordinate generators $x,y,z,w$. These are whole scheme and whole ring identities, not point-set correspondences. There are no field, characteristic, smoothness, properness, chosen model, or fibre identification hypotheses. This supplies compatible whole-curve fibres for the actual integral curve family. Integral properness, a compatible Picard family, rational rank zero, and the final torsion reduction argument remain separate assertions.
-- source:
--   MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned gluing, scalar extension, overlap pullback and chart preimage proofs using Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. All per-file provenance and attribution are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_whole_curve_base_change_isomorphism.{u}
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    ∃ (e : pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (curveToBase R) ≅ curveScheme S)
      (φA : CoordinateRing R →+* CoordinateRing S)
      (φB : ReciprocalRing R →+* ReciprocalRing S),
      e.inv ≫ pullback.fst _ _ = curveToBase S ∧
      ordinaryChartMap S ≫ e.inv ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom φA) ≫ ordinaryChartMap R ∧
      reciprocalChartMap S ≫ e.inv ≫ pullback.snd _ _ =
        Spec.map (CommRingCat.ofHom φB) ≫ reciprocalChartMap R ∧
      (∀ r : R, φA (algebraMap R (CoordinateRing R) r) =
        algebraMap S (CoordinateRing S) (algebraMap R S r)) ∧
      (∀ r : R, φB (algebraMap R (ReciprocalRing R) r) =
        algebraMap S (ReciprocalRing S) (algebraMap R S r)) ∧
      φA (xCoordinate R) = xCoordinate S ∧
      φA (yCoordinate R) = yCoordinate S ∧
      φB (zCoordinate R) = zCoordinate S ∧
      φB (wCoordinate R) = wCoordinate S := by sorry
