-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_ResidueLift_mem_R_of_pattern
-- name    : GlobalTheory.SymChain.ResidueLift.mem_R_of_pattern
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:10:34.57421+00:00
-- url     : https://prove2.me/theorems/dd12986f-8588-5fab-9a5c-22c9f58be651
-- title:
--   Residue Lift: mem R of pattern
-- statement:
--   The Residue Lift construction uses the mem R of pattern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsRootExchangeParabolicMulPrincipalCongruenc.lean#L24-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsRootExchangeParabolicMulPrincipalCongruenc.lean#L24-L62

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

theorem GlobalTheory.SymChain.ResidueLift.mem_R_of_pattern (r : GL (n ⊕ Fin c) k)
    (hr : ∀ a b : n ⊕ Fin c, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
      r.val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b) :
    r ∈ R k n c p := by sorry
