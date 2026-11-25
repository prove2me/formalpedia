-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NearCount_count_between
-- name    : GlobalTheory.DegCnt.NearCount.count_between
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:21.026387+00:00
-- url     : https://prove2.me/theorems/a696f85e-30ea-4a7b-92d8-989f4557f546
-- title:
--   Near Count: count between
-- statement:
--   The Near Count construction uses the count between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardLatticesNearReferenceLatticeLe.lean#L46-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardLatticesNearReferenceLatticeLe.lean#L46-L102

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
omit [Module K V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.NearCount.count_between (P : Submodule (𝓞 K) V) (n : Ideal (𝓞 K)) (hn : n ≠ ⊥) (e : ℕ) (v : Fin e → V)
    (hv : ∀ i, v i ∈ P) (hP : P ≤ n • P ⊔ Submodule.span (𝓞 K) (Set.range v)) :
    {L : Submodule (𝓞 K) V | n • P ≤ L ∧ L ≤ P}.encard ≤ ((Ideal.absNorm n ^ (e * e) : ℕ) : ℕ∞) := by sorry
