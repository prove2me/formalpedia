-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_DatCount_div_mem_dual
-- name    : GlobalTheory.DegCnt.DatCount.div_mem_dual
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:56:06.391312+00:00
-- url     : https://prove2.me/theorems/ea9f5cb3-817e-4912-9fbf-a43fdb151472
-- title:
--   Dat Count: div mem dual
-- statement:
--   The Dat Count construction uses the div mem dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L176-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L176-L186

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEmbeddedDataWithGivenFixedLattice
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DatCount
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [NumberField K]

theorem GlobalTheory.DegCnt.DatCount.div_mem_dual {H : HermSpace K V} {g : 𝓞 K} (hg : g ≠ 0) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (hΓ : IsModIso H g L' L Γ) {s y : V} (h : (s, y) ∈ Γ) :
    (algebraMap (𝓞 K) K g)⁻¹ • (s - y) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip (fixLat Γ) := by sorry
