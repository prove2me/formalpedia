-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_UnipPow_valuation_resCard_lt_one
-- name    : GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:09:32.41196+00:00
-- url     : https://prove2.me/theorems/3dbd4f55-ed3a-4cfd-8162-a8b31a32d472
-- title:
--   Unip Pow: valuation res Card lt one
-- statement:
--   The Unip Pow construction uses the valuation res Card lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RootExchangeUnipotentExistsResidueCardPowMemNhds.lean#L27-L36

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

theorem GlobalTheory.RootEx.UnipPow.valuation_resCard_lt_one : valuation k (resCard k : k) < 1 := by sorry
