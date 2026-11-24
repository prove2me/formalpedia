-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_locallyConstant_cutoff_closedEmbedding
-- name    : GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:36:42.933103+00:00
-- url     : https://prove2.me/theorems/5c6135a2-8e25-4147-bb08-e667280dfa05
-- title:
--   T: exists locally Constant cutoff closed Embedding
-- statement:
--   The T construction uses the exists locally Constant cutoff closed Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbeddingStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsLocallyConstantCutoffClosedEmbeddingStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsLocallyConstantCutoffClosedEmbeddingStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_locallyConstant_cutoff_closedEmbedding : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by sorry
