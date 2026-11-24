-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_RowSupport_exists_box
-- name    : GlobalTheory.RootEx.RowSupport.exists_box
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:28:15.487284+00:00
-- url     : https://prove2.me/theorems/d8a79b4a-458e-499e-8e7d-d7a162afed8b
-- title:
--   Row Support: exists box
-- statement:
--   The Row Support construction uses the exists box property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RowSupportUniform.lean#L12-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RowSupportUniform.lean#L12-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport

theorem GlobalTheory.RootEx.RowSupport.exists_box {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (W : Set (n → k)) (hW : W ∈ 𝓝 (0 : n → k)) :
    ∃ B : Set (n → k), IsCompact B ∧ ∀ u, u ∉ B → ∃ β ∈ W, ψ (u ⬝ᵥ β) ≠ 1 := by sorry
