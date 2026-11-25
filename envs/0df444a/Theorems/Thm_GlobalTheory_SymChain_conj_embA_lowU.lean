-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_conj_embA_lowU
-- name    : GlobalTheory.SymChain.conj_embA_lowU
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:08:43.844534+00:00
-- url     : https://prove2.me/theorems/d512702c-5b23-40e9-8561-f2a4441607c4
-- title:
--   Sym Chain: conj emb A low U
-- statement:
--   The Sym Chain construction uses the conj emb A low U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeRowUnipotentMemSourceLevel.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeRowUnipotentMemSourceLevel.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain

theorem GlobalTheory.SymChain.conj_embA_lowU {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (d : Fin c → kˣ)
    (C : Matrix (Fin c) n k) :
    embA n (GlobalTheory.SplitFlip.diagGL d) * lowU (diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) * C) *
      (embA n (GlobalTheory.SplitFlip.diagGL d))⁻¹ = lowU C := by sorry
