-- Prove2me | Theorems.Thm_GlobalTheory_CutOff_exists_nhds_one_mul_mem_iff
-- name    : GlobalTheory.CutOff.exists_nhds_one_mul_mem_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:33:09.949346+00:00
-- url     : https://prove2.me/theorems/fac211f1-6367-4171-a8ba-38a03ec246df
-- title:
--   Cut Off: exists nhds one mul mem iff
-- statement:
--   The Cut Off construction uses the exists nhds one mul mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbedding.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbedding.lean#L20-L31

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CutOff

theorem GlobalTheory.CutOff.exists_nhds_one_mul_mem_iff {R : Type} [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] {U : Set R} (hUo : IsOpen U) (hUk : IsCompact U) :
    ∃ W ∈ 𝓝 (1 : R), ∀ w ∈ W, ∀ x, w * x ∈ U ↔ x ∈ U := by sorry
