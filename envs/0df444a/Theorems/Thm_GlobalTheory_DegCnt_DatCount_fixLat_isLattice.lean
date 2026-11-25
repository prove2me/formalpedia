-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_DatCount_fixLat_isLattice
-- name    : GlobalTheory.DegCnt.DatCount.fixLat_isLattice
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:18:18.535487+00:00
-- url     : https://prove2.me/theorems/cc4f4e21-3ac5-40dc-a14c-81fdf3b9b32a
-- title:
--   Dat Count: fix Lat is Lattice
-- statement:
--   The Dat Count construction uses the fix Lat is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L155-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEmbeddedDataWithGivenFixedLattice.lean#L155-L172

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

theorem GlobalTheory.DegCnt.DatCount.fixLat_isLattice {H : HermSpace K V} {g : 𝓞 K} (hg : g ≠ 0) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (hL' : Submodule.IsLattice K L') (hL : Submodule.IsLattice K L)
    (hΓ : IsModIso H g L' L Γ) : Submodule.IsLattice K (fixLat Γ) := by sorry
