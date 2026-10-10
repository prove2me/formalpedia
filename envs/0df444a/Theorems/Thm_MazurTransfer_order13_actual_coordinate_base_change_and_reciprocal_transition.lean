-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_coordinate_base_change_and_reciprocal_transition
-- name    : MazurTransfer.order13_actual_coordinate_base_change_and_reciprocal_transition
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T01:34:19.855262+00:00
-- url     : https://prove2.me/theorems/57128473-15a5-4575-ad82-55b6bc04ecd5
-- title:
--   Actual chart base change and reciprocal transition compatibility
-- statement:
--   Let $R$ be any commutative ring and $S$ any commutative $R$-algebra. Let $A_R$ and $B_R$ be the actual quadratic coordinate algebras of the ordinary and reciprocal charts of the literal order-13 curve. Their coordinates are $x,y$ and $z,w$, respectively. There exist genuine $S$-algebra isomorphisms
--
--   $$S\otimes_R A_R\simeq A_S,\qquad S\otimes_R B_R\simeq B_S$$
--
--   that carry the four coordinate generators to their counterparts over $S$. They extend to ring maps on the principal-open overlap algebras $(A_R)_x$ and $(B_R)_z$. These maps agree with the chart maps on every element of each coordinate algebra and commute with both directions of the actual reciprocal transition
--
--   $$x=z^{-1},\qquad y=wz^{-3}.$$
--
--   The compatibility holds on the entire localized rings. No field, characteristic, smoothness, properness or chosen identification is a hypothesis. This supplies the algebraic gluing compatibility required to identify fibres of the actual integral curve; the resulting glued scheme isomorphism and compatible Picard family are separate assertions.
-- source:
--   MazurTheorem WIP, pin 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned base-change and localization compatibility proofs using Mathlib at 0df444a360eaa60ab8c11dca51a86af692955474. Per-file provenance and attribution are retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve

open Polynomial Algebra TensorProduct
open MazurTorsion.XOneThirteenAffineCurve
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_coordinate_base_change_and_reciprocal_transition.{u,v}
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    ∃ (eA : S ⊗[R] CoordinateRing R ≃ₐ[S] CoordinateRing S)
      (eB : S ⊗[R] ReciprocalRing R ≃ₐ[S] ReciprocalRing S)
      (φA : OrdinaryOverlapRing R →+* OrdinaryOverlapRing S)
      (φB : ReciprocalOverlapRing R →+* ReciprocalOverlapRing S),
      eA (1 ⊗ₜ[R] xCoordinate R) = xCoordinate S ∧
      eA (1 ⊗ₜ[R] yCoordinate R) = yCoordinate S ∧
      eB (1 ⊗ₜ[R] zCoordinate R) = zCoordinate S ∧
      eB (1 ⊗ₜ[R] wCoordinate R) = wCoordinate S ∧
      (∀ a : CoordinateRing R,
        φA (algebraMap (CoordinateRing R) (OrdinaryOverlapRing R) a) =
          algebraMap (CoordinateRing S) (OrdinaryOverlapRing S) (eA (1 ⊗ₜ[R] a))) ∧
      (∀ b : ReciprocalRing R,
        φB (algebraMap (ReciprocalRing R) (ReciprocalOverlapRing R) b) =
          algebraMap (ReciprocalRing S) (ReciprocalOverlapRing S) (eB (1 ⊗ₜ[R] b))) ∧
      φB.comp (ordinaryToReciprocal R).toRingHom =
        (ordinaryToReciprocal S).toRingHom.comp φA ∧
      φA.comp (reciprocalToOrdinary R).toRingHom =
        (reciprocalToOrdinary S).toRingHom.comp φB := by sorry
