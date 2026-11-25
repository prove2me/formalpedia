-- Prove2me | Theorems.Thm_GlobalTheory_Mass_ShortVector_idxN_span
-- name    : GlobalTheory.Mass.ShortVector.idxN_span
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:39:02.016618+00:00
-- url     : https://prove2.me/theorems/15e8c176-36de-4a55-aad7-5253dc3637e5
-- title:
--   Short Vector: idx N span
-- statement:
--   The Short Vector construction uses the idx N span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOne.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOne.lean#L19-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
omit [StarRing K] [Module K V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.Mass.ShortVector.idxN_span (x : V) (S : Submodule (𝓞 K) V) :
    idxN (Submodule.span (𝓞 K) {x}) S =
      Ideal.absNorm (S.comap (LinearMap.toSpanSingleton (𝓞 K) V x) : Ideal (𝓞 K)) := by sorry
