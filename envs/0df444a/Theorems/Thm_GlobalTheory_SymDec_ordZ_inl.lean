-- Prove2me | Theorems.Thm_GlobalTheory_SymDec_ordZ_inl
-- name    : GlobalTheory.SymDec.ordZ_inl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:16:29.242559+00:00
-- url     : https://prove2.me/theorems/576168e1-a942-4ab0-95e9-71e19a875dfc
-- title:
--   Sym Dec: ord Z inl
-- statement:
--   The Sym Dec construction uses the ord Z inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L59-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/TypeFrameConjugationDecomposition.lean#L59-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_TypeFrameConjugationDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymDec
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] {κ c : ℕ} (t : Type) [Fintype t] [DecidableEq t]

theorem GlobalTheory.SymDec.ordZ_inl (hc : 0 + c = c) (i : Fin κ) : ordZ t hc (Sum.inl i) = Sum.inl (Sum.inl (Sum.inl i)) := by sorry
