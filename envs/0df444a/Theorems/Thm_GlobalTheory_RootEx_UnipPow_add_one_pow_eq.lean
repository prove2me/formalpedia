-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnipPow_add_one_pow_eq
-- name    : GlobalTheory.RootEx.UnipPow.add_one_pow_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:09:29.418501+00:00
-- url     : https://prove2.me/theorems/c5e227fa-e548-44e4-8e23-9fbf5742e1ff
-- title:
--   Unip Pow: add one pow eq
-- statement:
--   The Unip Pow construction uses the add one pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L62-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L62-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.RootEx.UnipPow.add_one_pow_eq {R : Type} [Ring R] {a : R} {d : ℕ} (ha : a ^ d = 0) (M : ℕ) :
    (a + 1) ^ M = ∑ i ∈ Finset.range d, (M.choose i) • a ^ i := by sorry
