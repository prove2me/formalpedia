-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_pt_mulVec_inX
-- name    : GlobalTheory.RootEx.UnfoldShape.pt_mulVec_inX
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:53.386029+00:00
-- url     : https://prove2.me/theorems/47a09f94-b72e-423b-ae2f-fa5b21d60d11
-- title:
--   Unfold Shape: pt mul Vec in X
-- statement:
--   The Unfold Shape construction uses the pt mul Vec in X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L276-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L276-L279

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_ExponentTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms
variable {k : Type} [Field k] [ValuativeRel k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.RootEx.UnfoldShape.pt_mulVec_inX (x₀ : Matrix n n' k) (y : Fin c → (n ⊕ Fin c → k)) (v : n' → k) :
    pt x₀ y *ᵥ inX k n' (c + 1) v = inX k n c (x₀ *ᵥ v) := by sorry
