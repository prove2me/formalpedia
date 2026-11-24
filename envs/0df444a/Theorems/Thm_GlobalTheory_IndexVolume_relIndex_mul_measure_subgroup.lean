-- Prove2me | Theorems.Thm_GlobalTheory_IndexVolume_relIndex_mul_measure_subgroup
-- name    : GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:53:44.211705+00:00
-- url     : https://prove2.me/theorems/54fbbb25-cdaf-46f0-82d9-b956bb7f6e13
-- title:
--   Index Volume: rel Index mul measure subgroup
-- statement:
--   The Index Volume construction uses the rel Index mul measure subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexMulMatrixVolumeOpenSubgroupIntegralGL.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RelIndexMulMatrixVolumeOpenSubgroupIntegralGL.lean#L10-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_BorelParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
open scoped Pointwise
open GlobalTheory GlobalTheory.IndexVolume

theorem GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (H L : Subgroup G) (hHL : H ≤ L) [(H.subgroupOf L).FiniteIndex]
    (hH : MeasurableSet (H : Set G)) (μ : Measure G) [μ.IsMulLeftInvariant] :
    (H.relIndex L : ENNReal) * μ H = μ L := by sorry
