-- Prove2me | Theorems.Thm_GlobalTheory_SmallLift_map_maximalIdeal_quot
-- name    : GlobalTheory.SmallLift.map_maximalIdeal_quot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:34.171846+00:00
-- url     : https://prove2.me/theorems/144c5461-b069-486c-bc7d-41a3d1370515
-- title:
--   Small Lift: map maximal Ideal quot
-- statement:
--   The Small Lift construction uses the map maximal Ideal quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStalkRetractionOfSmallLifting.lean#L62-L65

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

theorem GlobalTheory.SmallLift.map_maximalIdeal_quot {A : Type} [CommRing A] [IsLocalRing A] (J : Ideal A)
    [IsLocalRing (A ⧸ J)] :
    (maximalIdeal A).map (Ideal.Quotient.mk J) = maximalIdeal (A ⧸ J) := by sorry
