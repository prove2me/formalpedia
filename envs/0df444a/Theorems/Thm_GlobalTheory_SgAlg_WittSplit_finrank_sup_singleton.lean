-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_finrank_sup_singleton
-- name    : GlobalTheory.SgAlg.WittSplit.finrank_sup_singleton
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:31.525607+00:00
-- url     : https://prove2.me/theorems/3c4a7d1b-8b73-4ba5-bcf0-8aeb53a39c3d
-- title:
--   Witt Split: finrank sup singleton
-- statement:
--   The Witt Split construction uses the finrank sup singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L28-L34

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

theorem GlobalTheory.SgAlg.WittSplit.finrank_sup_singleton (U : Submodule K V) {v : V} (hv : v ∉ U) :
    finrank K (U ⊔ K ∙ v : Submodule K V) = finrank K U + 1 := by sorry
