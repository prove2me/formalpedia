-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilMix_isTest_rowAct
-- name    : GlobalTheory.JR.WeilMix.isTest_rowAct
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:37:48.617665+00:00
-- url     : https://prove2.me/theorems/43a4ca98-d3f9-4cb1-8eaf-9992b9df3cf2
-- title:
--   Weil Mix: is Test row Act
-- statement:
--   The Weil Mix construction uses the is Test row Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWeilRepSL2GlBorderedBlock.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsWeilRepSL2GlBorderedBlock.lean#L29-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportMixedModelPartialStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumnStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelWeylElementEqPartialFourierStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsWeilRepSL2GlBorderedBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilMix
variable {r : ℕ} {F : Type} [NontriviallyNormedField F]

theorem GlobalTheory.JR.WeilMix.isTest_rowAct (g : SpecialLinearGroup (Fin 2) F) (h : Gl r F → ℂ) (hh : IsTest h) : IsTest (rowAct g h) := by sorry
