-- Prove2me | Theorems.Thm_GlobalTheory_SmallLift_isLocalRing_quot
-- name    : GlobalTheory.SmallLift.isLocalRing_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:24.908915+00:00
-- url     : https://prove2.me/theorems/a7749354-45e5-4385-9eaf-b1c28fe540f6
-- title:
--   Small Lift: is Local Ring quot
-- statement:
--   The Small Lift construction uses the is Local Ring quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L57-L60

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

theorem GlobalTheory.SmallLift.isLocalRing_quot {A : Type} [CommRing A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (A ⧸ maximalIdeal A ^ (n + 1)) := by sorry
