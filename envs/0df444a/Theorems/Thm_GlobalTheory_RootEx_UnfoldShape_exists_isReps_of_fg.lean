-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_exists_isReps_of_fg
-- name    : GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:21:24.585567+00:00
-- url     : https://prove2.me/theorems/98d0da44-3a0c-46ed-b8b2-807ee27ee8a5
-- title:
--   Unfold Shape: exists is Reps of fg
-- statement:
--   The Unfold Shape construction uses the exists is Reps of fg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsRepsOfFg.lean#L10-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsRepsOfFg.lean#L10-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsRepsOfFg
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

theorem GlobalTheory.RootEx.UnfoldShape.exists_isReps_of_fg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (hϖ : Irreducible ϖ) (M : Submodule 𝒪[k] (ι → k)) (hM : M.FG) :
    ∃ T : Finset (ι → k), IsReps ϖ M T := by sorry
