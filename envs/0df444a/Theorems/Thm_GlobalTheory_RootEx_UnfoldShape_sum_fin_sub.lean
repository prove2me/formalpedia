-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_sum_fin_sub
-- name    : GlobalTheory.RootEx.UnfoldShape.sum_fin_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:43.267852+00:00
-- url     : https://prove2.me/theorems/007a28c6-e0bd-4215-be7c-79f350babba6
-- title:
--   Unfold Shape: sum fin sub
-- statement:
--   The Unfold Shape construction uses the sum fin sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/VolFreePerLatStdLat.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_VolFreePerLatStdLat
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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnfoldShape

theorem GlobalTheory.RootEx.UnfoldShape.sum_fin_sub (c j : ℕ) (hj : j ≤ c) :
    ∑ l : Fin c, (j - (l.val + 1)) = j * (j - 1) / 2 := by sorry
