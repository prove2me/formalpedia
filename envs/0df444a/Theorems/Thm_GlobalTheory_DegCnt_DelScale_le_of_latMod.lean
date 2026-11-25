-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_DelScale_le_of_latMod
-- name    : GlobalTheory.DegCnt.DelScale.le_of_latMod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:09.505436+00:00
-- url     : https://prove2.me/theorems/1e1527bf-c865-451d-84a2-824559e8d33d
-- title:
--   Del Scale: le of lat Mod
-- statement:
--   The Del Scale construction uses the le of lat Mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfLatMod.lean#L148-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfLatMod.lean#L148-L151

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfLatMod
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.DelScale
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {S I C : Submodule K V} (p : V →ₗ[K] V) (hCS : C ≤ S) (hpC : ∀ x ∈ S, p x ∈ C)
  (hpI : ∀ x, x - p x ∈ I) (hI : ∀ x ∈ I, p x = 0) (hC : ∀ x ∈ C, p x = x)
omit [NumberField K] [StarRing K] [FiniteDimensional K V]

theorem GlobalTheory.DegCnt.DelScale.le_of_latMod {M : Submodule (𝓞 K) V} (hM : IsLatMod M S I) :
    rs (𝓞 K) I ≤ M ∧ M ≤ rs (𝓞 K) S := by sorry
