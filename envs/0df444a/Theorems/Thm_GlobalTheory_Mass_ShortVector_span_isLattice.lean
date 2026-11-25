-- Prove2me | Theorems.Thm_GlobalTheory_Mass_ShortVector_span_isLattice
-- name    : GlobalTheory.Mass.ShortVector.span_isLattice
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:52:40.4766+00:00
-- url     : https://prove2.me/theorems/f9d09959-aac1-4e2d-a714-ed61114de50e
-- title:
--   Short Vector: span is Lattice
-- statement:
--   The Short Vector construction uses the span is Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOne.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsShortVectorIntegralHermitianLatticeRankOne.lean#L45-L50

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
omit [StarRing K]

theorem GlobalTheory.Mass.ShortVector.span_isLattice (h1 : Module.finrank K V = 1) {x : V} (hx : x ≠ 0) :
    Submodule.IsLattice K (Submodule.span (𝓞 K) {x}) := by sorry
