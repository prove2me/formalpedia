-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_ResidueLift_of_blockIx_lt
-- name    : GlobalTheory.SymChain.ResidueLift.of_blockIx_lt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:40.140667+00:00
-- url     : https://prove2.me/theorems/1304efc1-ca41-5e46-9a36-8d3f1c550ceb
-- title:
--   Residue Lift: of block Ix lt
-- statement:
--   The Residue Lift construction uses the of block Ix lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsRootExchangeParabolicMulPrincipalCongruenc.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsRootExchangeParabolicMulPrincipalCongruenc.lean#L14-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_TypeChainPrincipalEntryNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRootExchangeParabolicMulPrincipalCongruenc
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
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.ResidueLift
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

theorem GlobalTheory.SymChain.ResidueLift.of_blockIx_lt {a b : n ⊕ Fin c} (h : blockIx p b < blockIx p a) :
    lev p b ≤ lev p a ∧ ¬ (a.isLeft = true ∧ b.isLeft = true) ∧ a ≠ b := by sorry
