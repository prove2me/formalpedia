-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_QuotLinear_finiteOnCompacts_volN
-- name    : GlobalTheory.RootEx.QuotLinear.finiteOnCompacts_volN
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:26:02.078294+00:00
-- url     : https://prove2.me/theorems/dd88b0cf-02e4-4005-afdd-cd42bf41e62c
-- title:
--   Quot Linear: finite On Compacts vol N
-- statement:
--   The Quot Linear construction uses the finite On Compacts vol N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralLinear.lean#L64-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/QuotientIntegralLinear.lean#L64-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralLinear
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.QuotLinear
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
variable [MeasurableSpace k] [BorelSpace k]

theorem GlobalTheory.RootEx.QuotLinear.finiteOnCompacts_volN (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (volN ν n c p) := by sorry
