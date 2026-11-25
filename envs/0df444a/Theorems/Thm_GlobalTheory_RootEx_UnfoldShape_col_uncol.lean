-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_col_uncol
-- name    : GlobalTheory.RootEx.UnfoldShape.col_uncol
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T10:34:56.758606+00:00
-- url     : https://prove2.me/theorems/f3bbf3cd-b7a8-5e07-86de-e2335eb1375e
-- title:
--   Unfold Shape: col uncol
-- statement:
--   The Unfold Shape construction uses the col uncol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L238-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L238-L247

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
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem GlobalTheory.RootEx.UnfoldShape.col_uncol {y : Fin c → (n ⊕ Fin c → k)} (hy : ∀ i, y i ∈ Yle k n c (i.val + 1)) :
    col (uncol n' y) = y := by sorry
