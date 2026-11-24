-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_basePt_mulVec
-- name    : GlobalTheory.RootEx.UnfoldShape.basePt_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:32:04.400696+00:00
-- url     : https://prove2.me/theorems/b3f0a797-11ec-4380-a32a-1c514f5ef1d4
-- title:
--   Unfold Shape: base Pt mul Vec
-- statement:
--   The Unfold Shape construction uses the base Pt mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L259-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L259-L271

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
omit [ValuativeRel k] [Fintype n] [DecidableEq n] [DecidableEq n']

theorem GlobalTheory.RootEx.UnfoldShape.basePt_mulVec (x₀ : Matrix n n' k) (v : n' ⊕ Fin (c + 1) → k) :
    basePt c x₀ *ᵥ v = Sum.elim (x₀ *ᵥ fun s => v (Sum.inl s)) fun l => v (Sum.inr l.castSucc) := by sorry
