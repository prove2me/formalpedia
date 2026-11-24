-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_inj_of_left
-- name    : GlobalTheory.SgAlg.WittSplit.inj_of_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:54:55.691241+00:00
-- url     : https://prove2.me/theorems/c3d48e88-669c-4dfc-a7e8-cd73745df839
-- title:
--   Witt Split: inj of left
-- statement:
--   The Witt Split construction uses the inj of left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L67-L73

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

theorem GlobalTheory.SgAlg.WittSplit.inj_of_left (u : Matrix m k F) (h : ∃ L : Matrix k m F, L * u = 1) :
    Function.Injective (Matrix.toLin' u) := by sorry
