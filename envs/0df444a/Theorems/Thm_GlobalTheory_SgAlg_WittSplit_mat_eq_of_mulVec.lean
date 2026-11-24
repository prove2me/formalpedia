-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_mat_eq_of_mulVec
-- name    : GlobalTheory.SgAlg.WittSplit.mat_eq_of_mulVec
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:55.3003+00:00
-- url     : https://prove2.me/theorems/9f3276ea-9516-49ce-883b-b93a483ea203
-- title:
--   Witt Split: mat eq of mul Vec
-- statement:
--   The Witt Split construction uses the mat eq of mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L75-L77

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
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem GlobalTheory.SgAlg.WittSplit.mat_eq_of_mulVec {p q : Type} [Fintype q] [DecidableEq q] (M N : Matrix p q F)
    (h : ∀ c, M *ᵥ c = N *ᵥ c) : M = N := by sorry
