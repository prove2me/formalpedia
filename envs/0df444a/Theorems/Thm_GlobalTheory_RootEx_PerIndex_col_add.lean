-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_PerIndex_col_add
-- name    : GlobalTheory.RootEx.PerIndex.col_add
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T10:39:22.112811+00:00
-- url     : https://prove2.me/theorems/3a5a1628-a185-499d-a878-8882484e251a
-- title:
--   Per Index: col add
-- statement:
--   The Per Index construction uses the col add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexPerLat.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexPerLat.lean#L12-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexPerLat
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
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.PerIndex
variable {k : Type} [Field k] [ValuativeRel k] {n : Type}

theorem GlobalTheory.RootEx.PerIndex.col_add (n' : Type) {c : ℕ}
    (e f : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free 1 rs} → k) (i : Fin c) :
    UnfoldShape.col (n' := n') (e + f) i
      = UnfoldShape.col (n' := n') e i + UnfoldShape.col (n' := n') f i := by sorry
