-- Prove2me | Theorems.Thm_GlobalTheory_LocFlat_SuppColProof_det_colE
-- name    : GlobalTheory.LocFlat.SuppColProof.det_colE
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:00.282691+00:00
-- url     : https://prove2.me/theorems/8c39a709-e3aa-5805-ba3c-9682e304cda2
-- title:
--   Supp Col Proof: det col E
-- statement:
--   The Supp Col Proof construction uses the det col E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnSupportOfOneIndexAtSymPosition.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatColumnSupportOfOneIndexAtSymPosition.lean#L11-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnSupportOfOneIndexAtSymPosition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.SuppColProof

theorem GlobalTheory.LocFlat.SuppColProof.det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by sorry
