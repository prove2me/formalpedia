-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_exists_left_inv_unit
-- name    : GlobalTheory.SgAlg.WittSplit.exists_left_inv_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:18.992349+00:00
-- url     : https://prove2.me/theorems/84b840aa-bcba-4bac-a673-f5f0bba3b2d9
-- title:
--   Witt Split: exists left inv unit
-- statement:
--   The Witt Split construction uses the exists left inv unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L79-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L79-L106

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

theorem GlobalTheory.SgAlg.WittSplit.exists_left_inv_unit (u u' : Matrix m k F) (hu : ∃ L : Matrix k m F, L * u = 1)
    (hu' : ∃ L : Matrix k m F, L * u' = 1) : ∃ L : Matrix k m F, L * u = 1 ∧ IsUnit (L * u').det := by sorry
