-- Prove2me | Theorems.Thm_GlobalTheory_DominatesStalk_comap
-- name    : GlobalTheory.DominatesStalk.comap
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:11.289507+00:00
-- url     : https://prove2.me/theorems/4d69d171-0d63-487d-aa29-f3f9c9107bef
-- title:
--   Dominates Stalk: comap
-- statement:
--   The Dominates Stalk construction uses the comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L381-L389
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L381-L389

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {X X' S : Scheme.{u}} [IsIntegral X] [IsIntegral X']
variable {W : ValuationSubring X.functionField} {x : X}

theorem GlobalTheory.DominatesStalk.comap (h : DominatesStalk W x) (f : X ⟶ X') [IsDominant f] :
    DominatesStalk (W.comap (functionFieldMap f)) (f x) := by sorry
