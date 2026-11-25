-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnfoldShape_stabiliser_finite_cosets_mod
-- name    : GlobalTheory.RootEx.UnfoldShape.stabiliser_finite_cosets_mod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:46.078318+00:00
-- url     : https://prove2.me/theorems/b0d4363d-8e3d-5742-8403-106e0fb628ca
-- title:
--   Unfold Shape: stabiliser finite cosets mod
-- statement:
--   The Unfold Shape construction uses the stabiliser finite cosets mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/StabiliserFiniteCosetsMod.lean#L10-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/StabiliserFiniteCosetsMod.lean#L10-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ScaledBasisMemChainLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_StabiliserFiniteCosetsMod
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

theorem GlobalTheory.RootEx.UnfoldShape.stabiliser_finite_cosets_mod (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (ϖ : 𝒪[k])
    (M : Submodule 𝒪[k] (ι → k)) (S : Finset (ι → k)) (hM : M.FG) (hS : IsReps ϖ M S) :
    ∃ T : Finset (GL ι k), (∀ t ∈ T, act t M = M) ∧ ∀ t : GL ι k, act t M = M →
      ∃ t₀ ∈ T, ∃ j : GL ι k, act j M = M ∧ MapsInto (j.val - 1) M (ϖ • M) ∧ t = t₀ * j := by sorry
