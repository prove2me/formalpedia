-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedExp_eventually_box_subset
-- name    : GlobalTheory.AdaptedExp.eventually_box_subset
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:57.941238+00:00
-- url     : https://prove2.me/theorems/74304a91-b324-4927-8da2-eaea9fece897
-- title:
--   Adapted Exp: eventually box subset
-- statement:
--   The Adapted Exp construction uses the eventually box subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAdaptedExponentSchwartzBruhatLastColumn.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAdaptedExponentSchwartzBruhatLastColumn.lean#L58-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAdaptedExponentSchwartzBruhatLastColumn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.AdaptedExp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type}

theorem GlobalTheory.AdaptedExp.eventually_box_subset [Fintype n] {ϖ : kˣ} (h : IsUnif ϖ) {U : Set (n → k)}
    (hU : U ∈ 𝓝 (0 : n → k)) :
    ∀ᶠ e : ℕ in Filter.atTop, ∀ z ∈ box n (ϖ ^ e), z ∈ U := by sorry
