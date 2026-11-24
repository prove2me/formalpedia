-- Prove2me | Theorems.Thm_GlobalTheory_SmallLift_map_closedPoint
-- name    : GlobalTheory.SmallLift.map_closedPoint
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:15:07.834583+00:00
-- url     : https://prove2.me/theorems/ae9f7dec-ae1f-4ec2-926c-794009ce89ec
-- title:
--   Small Lift: map closed Point
-- statement:
--   The Small Lift construction uses the map closed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L9-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L9-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStalkRetractionOfSmallLifting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.SmallLift

theorem GlobalTheory.SmallLift.map_closedPoint {X : Scheme.{0}} {x : X} {R : CommRingCat.{0}} [IsLocalRing R]
    (φ : X.presheaf.stalk x ⟶ R) [IsLocalHom φ.hom] :
    (Spec.map φ ≫ X.fromSpecStalk x) (closedPoint R) = x := by sorry
