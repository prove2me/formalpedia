-- Prove2me | Theorems.Thm_GlobalTheory_SmallPoint_exists_root_norm_lt
-- name    : GlobalTheory.SmallPoint.exists_root_norm_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:50.202802+00:00
-- url     : https://prove2.me/theorems/8c0a05bd-dd04-4561-b652-038ac190afd3
-- title:
--   Small Point: exists root norm lt
-- statement:
--   The Small Point construction uses the exists root norm lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComplexPointNormLtOfNotIsUnit.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsComplexPointNormLtOfNotIsUnit.lean#L50-L58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SpecialisationNumberFieldAndCountableValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PowCardLeNormProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsComplexPointNormLtOfNotIsUnit
import Theorems.Thm_GlobalTheory_RootNormLowerBound_exists_root_norm_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Filter Topology
open GlobalTheory
open GlobalTheory.SmallPoint

theorem GlobalTheory.SmallPoint.exists_root_norm_lt {F : ℂ[X]} (hF : F.Monic) {ε : ℝ} (hε : 0 < ε)
    (h : ‖F.coeff 0‖ < ε ^ F.natDegree) : ∃ t, F.IsRoot t ∧ ‖t‖ < ε := by sorry
