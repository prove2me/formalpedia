-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NearCount_line_cyclic
-- name    : GlobalTheory.DegCnt.NearCount.line_cyclic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:24.789694+00:00
-- url     : https://prove2.me/theorems/14a8bc3e-a942-4630-8e7d-18a94e963666
-- title:
--   Near Count: line cyclic
-- statement:
--   The Near Count construction uses the line cyclic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardLatticesNearReferenceLatticeLe.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardLatticesNearReferenceLatticeLe.lean#L15-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_DedekindLFunctions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EncardLatticesNearReferenceLatticeLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.NearCount
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.NearCount.line_cyclic (I : FractionalIdeal (𝓞 K)⁰ K) (v : V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) :
    ∃ u ∈ line (I : Submodule (𝓞 K) K) v,
      line (I : Submodule (𝓞 K) K) v ≤ n • line (I : Submodule (𝓞 K) K) v ⊔ Submodule.span (𝓞 K) {u} := by sorry
