-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedExp_eventually_subset_cball
-- name    : GlobalTheory.AdaptedExp.eventually_subset_cball
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:10:45.768857+00:00
-- url     : https://prove2.me/theorems/3e54a3c8-8361-4711-b2a4-8994a80a59c8
-- title:
--   Adapted Exp: eventually subset cball
-- statement:
--   The Adapted Exp construction uses the eventually subset cball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAdaptedExponentSchwartzBruhatLastColumn.lean#L20-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAdaptedExponentSchwartzBruhatLastColumn.lean#L20-L41

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

theorem GlobalTheory.AdaptedExp.eventually_subset_cball {ϖ : kˣ} (h : IsUnif ϖ) {K : Set k} (hK : IsCompact K) :
    ∀ᶠ e : ℕ in Filter.atTop, K ⊆ cball (ϖ ^ e)⁻¹ := by sorry
