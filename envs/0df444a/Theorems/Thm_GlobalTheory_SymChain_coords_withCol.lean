-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_coords_withCol
-- name    : GlobalTheory.SymChain.coords_withCol
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:44.123304+00:00
-- url     : https://prove2.me/theorems/17501a27-0509-50b7-842b-42fa4b65bf04
-- title:
--   Sym Chain: coords with Col
-- statement:
--   The Sym Chain construction uses the coords with Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainOneCouplingCosetOfPattern.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainOneCouplingCosetOfPattern.lean#L26-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
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
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] {ι ι' n n' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
  [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
omit [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

theorem GlobalTheory.SymChain.coords_withCol (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin 0) (ord' : ι' ≃ n' ⊕ Fin (0 + 1)) (x₀ : Matrix n n' k)
    (y : n → k) : (typeFrame ϖ ord).coords (typeFrame ϖ ord') (withCol x₀ y) =
      (withCol x₀ ((ϖ : k) • y)).submatrix ord ord' := by sorry
