-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_NearCount_smul_injective
-- name    : GlobalTheory.DegCnt.NearCount.smul_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:26:24.331155+00:00
-- url     : https://prove2.me/theorems/a4d85f9a-78f5-461b-9f99-6deb8c68b55d
-- title:
--   Near Count: smul injective
-- statement:
--   The Near Count construction uses the smul injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardLatticesNearReferenceLatticeLe.lean#L104-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/EncardLatticesNearReferenceLatticeLe.lean#L104-L119

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

theorem GlobalTheory.DegCnt.NearCount.smul_injective (m : Ideal (𝓞 K)) (hm : m ≠ ⊥) :
    Function.Injective fun P : Submodule (𝓞 K) V => m • P := by sorry
