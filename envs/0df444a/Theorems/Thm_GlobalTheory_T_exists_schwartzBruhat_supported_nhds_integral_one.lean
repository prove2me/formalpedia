-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_schwartzBruhat_supported_nhds_integral_one
-- name    : GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:41.748713+00:00
-- url     : https://prove2.me/theorems/1870327b-bbf7-4d4b-8a2d-1e14af9a6044
-- title:
--   T: exists schwartz Bruhat supported nhds integral one
-- statement:
--   The T construction uses the exists schwartz Bruhat supported nhds integral one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOne
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_schwartzBruhat_supported_nhds_integral_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by sorry
