-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_isPrincipal_mul_classRep
-- name    : GlobalTheory.existsUnique_isPrincipal_mul_classRep
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:17.81086+00:00
-- url     : https://prove2.me/theorems/02f7ca44-2248-4ace-a9e8-96ac4d3438aa
-- title:
--   Global Theory: exists Unique is Principal mul class Rep
-- statement:
--   The Global Theory construction uses the exists Unique is Principal mul class Rep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TsumIdealEqSumClassGroup.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TsumIdealEqSumClassGroup.lean#L10-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

theorem GlobalTheory.existsUnique_isPrincipal_mul_classRep {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c))) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    ∃! c, (I * (b c : Ideal (𝓞 K))).IsPrincipal := by sorry
