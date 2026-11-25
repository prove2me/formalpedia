-- Prove2me | Theorems.Thm_GlobalTheory_DominatesStalk_eq_top_iff
-- name    : GlobalTheory.DominatesStalk.eq_top_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:13.197002+00:00
-- url     : https://prove2.me/theorems/f22dac3a-daad-51a9-aa4a-097b80539813
-- title:
--   Dominates Stalk: eq top iff
-- statement:
--   The Dominates Stalk construction uses the eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L299-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsValuationSubringDominatingSubring.lean#L299-L317

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

theorem GlobalTheory.DominatesStalk.eq_top_iff (h : DominatesStalk W x) : W = ⊤ ↔ x = genericPoint X := by sorry
