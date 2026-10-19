-- Prove2me | Theorems.Thm_MazurTransfer_order13_overlap_transitions_commute_with_base_change
-- name    : MazurTransfer.order13_overlap_transitions_commute_with_base_change
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T03:13:36.65745+00:00
-- url     : https://prove2.me/theorems/0724f5c8-6776-4811-99ee-7db6347e5880
-- title:
--   Both actual reciprocal overlap transitions commute with base change
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. Let $A_R,B_R$ be the two coordinate rings of the actual order-thirteen curve, and let $t_R:A_R[x_R^{-1}]\to B_R[z_R^{-1}]$ and $s_R:B_R[z_R^{-1}]\to A_R[x_R^{-1}]$ be its specified inverse overlap transitions. If $\lambda_A,\lambda_B$ are the actual overlap base-change maps, then
--   $$\lambda_B\circ t_R=t_S\circ\lambda_A,\qquad\lambda_A\circ s_R=s_S\circ\lambda_B.$$
--
--   The identities hold on the entire localization rings. They supply the compatibility needed to glue the actual chart maps into the curve base-change morphism.
-- source:
--   Exact checked proofs in MazurTheorem Order13ReciprocalTransitionBaseChange.lean, ordinaryTransition_natural and reciprocalTransition_natural, with their original helper arguments. The Lean syntax oracles preserve all proof bodies and make proof-only helpers private; the new conclusion is the conjunction of the two complete original contracts. The proof imports the public merged coordinate and localization map interface. Vas and contributors, Apache-2.0.

import Definitions.Def_MazurTransfer_Order13CoordinateBaseChangeMaps
open MazurTransfer.Order13CoordinateBaseChange
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
universe u v

theorem MazurTransfer.order13_overlap_transitions_commute_with_base_change (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S] :
    (reciprocalOverlapRingMap R S).comp (ordinaryToReciprocal R).toRingHom =
      (ordinaryToReciprocal S).toRingHom.comp (ordinaryOverlapRingMap R S) ∧
    (ordinaryOverlapRingMap R S).comp (reciprocalToOrdinary R).toRingHom =
      (reciprocalToOrdinary S).toRingHom.comp (reciprocalOverlapRingMap R S)  := by sorry
