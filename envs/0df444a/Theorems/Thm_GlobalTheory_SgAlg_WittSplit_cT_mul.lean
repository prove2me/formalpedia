-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_cT_mul
-- name    : GlobalTheory.SgAlg.WittSplit.cT_mul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:24.886479+00:00
-- url     : https://prove2.me/theorems/17ba81d1-b9ef-46cc-9cd5-bbb5533c5bd2
-- title:
--   Witt Split: c T mul
-- statement:
--   The Witt Split construction uses the c T mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L154-L156

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
variable {E : Type} [CommRing E] (σ : E →+* E)

theorem GlobalTheory.SgAlg.WittSplit.cT_mul {p q r : Type} [Fintype q] (A : Matrix p q E) (B : Matrix q r E) :
    cT σ (A * B) = cT σ B * cT σ A := by sorry
