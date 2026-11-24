-- Prove2me | Theorems.Thm_GlobalTheory_LatPair_Red_residue_smul
-- name    : GlobalTheory.LatPair.Red.residue_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:58:46.832615+00:00
-- url     : https://prove2.me/theorems/db3bcad3-831a-4787-a791-e110bf2e55a4
-- title:
--   Red: residue smul
-- statement:
--   The Red construction uses the residue smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L350-L350
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/ExistsGlOfEquiv.lean#L350-L350

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
open GlobalTheory.LatPair.Red
variable (L : Submodule 𝒪[k] (n → k))
variable {L}

theorem GlobalTheory.LatPair.Red.residue_smul (s : 𝒪[k]) (x : Red L) : residue 𝒪[k] s • x = s • x := by sorry
