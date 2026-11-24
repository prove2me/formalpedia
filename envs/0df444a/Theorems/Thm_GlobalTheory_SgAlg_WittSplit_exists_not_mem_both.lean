-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_not_mem_both
-- name    : GlobalTheory.SgAlg.WittSplit.exists_not_mem_both
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:45.537021+00:00
-- url     : https://prove2.me/theorems/f560b122-407a-4d87-a6a2-13ab9f9ed466
-- title:
--   Witt Split: exists not mem both
-- statement:
--   The Witt Split construction uses the exists not mem both property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L12-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L12-L26

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem GlobalTheory.SgAlg.WittSplit.exists_not_mem_both (U U' : Submodule K V) (h : finrank K U = finrank K U') (hU : U ≠ ⊤) :
    ∃ v, v ∉ U ∧ v ∉ U' := by sorry
