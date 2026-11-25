-- Prove2me | Theorems.Thm_GlobalTheory_TraceCount_proj_rank
-- name    : GlobalTheory.TraceCount.proj_rank
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T05:16:55.048691+00:00
-- url     : https://prove2.me/theorems/f42e178b-90d2-5121-9d51-6b454113384b
-- title:
--   Trace Count: proj rank
-- statement:
--   The Trace Count construction uses the proj rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardSublatticesIndexFixedTraceLe.lean#L122-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardSublatticesIndexFixedTraceLe.lean#L122-L130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexCongruenceSubgroupLeAbsNormPow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardSublatticesIndexFixedTraceLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.TraceCount

theorem GlobalTheory.TraceCount.proj_rank {K W : Type} [Field K] [NumberField K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (C : Submodule (𝓞 K) W) (hC : C.FG) :
    Module.Finite (𝓞 K) C ∧ Module.Projective (𝓞 K) C ∧ Module.finrank (𝓞 K) C ≤ Module.finrank K W := by sorry
