-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_col_mem_Yle
-- name    : GlobalTheory.RootEx.UnfoldShape.col_mem_Yle
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:49.80532+00:00
-- url     : https://prove2.me/theorems/be3266d7-348d-5e72-8b18-e6f278374042
-- title:
--   Unfold Shape: col mem Yle
-- statement:
--   The Unfold Shape construction uses the col mem Yle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L231-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ScaledBasisMemChainLattice.lean#L231-L236

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

theorem GlobalTheory.RootEx.UnfoldShape.col_mem_Yle (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    col e i ∈ Yle k n c (i.val + 1) := by sorry
