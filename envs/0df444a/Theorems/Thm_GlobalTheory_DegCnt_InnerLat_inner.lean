-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_InnerLat_inner
-- name    : GlobalTheory.DegCnt.InnerLat.inner
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:28.154954+00:00
-- url     : https://prove2.me/theorems/9a7f844a-e84b-4bb0-973e-194804d37b9a
-- title:
--   Inner Lat: inner
-- statement:
--   The Inner Lat construction uses the inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairInnerLatticesUnimodularPrimitive.lean#L126-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairInnerLatticesUnimodularPrimitive.lean#L126-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairNormalFormGeometrySummaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermFramePairInnerLatticesUnimodularPrimitive
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.InnerLat
open GlobalTheory.UnimodQuot
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {H : HermSpace K V} {r : ℕ}

theorem GlobalTheory.DegCnt.InnerLat.inner [FiniteDimensional K V] (F : FlagD H r) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    (hlead : lead F Λ (Fin.last r) = 1) {S Z I : Submodule K V} (hXS : F.X ≤ S) (hz : F.z ∈ perp H S)
    (hZ : ∀ z ∈ Z, z ∈ perp H S)
    (hI : ∀ x ∈ F.X, (∀ w ∈ S ⊔ Z, H.B w x = 0) ↔ x ∈ I) (hIX : I ≤ F.X)
    (hs : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ S ⊔ Z, H.B v (w - x) = 0) :
    IsUnimodMod H (rs (𝓞 K) (perp H S) ⊓ (Λ ⊔ rs (𝓞 K) F.X)) (perp H S) I ∧
      ∀ t : K, t • F.z ∈ rs (𝓞 K) (perp H S) ⊓ (Λ ⊔ rs (𝓞 K) F.X) ↔ t ∈ (1 : Submodule (𝓞 K) K) := by sorry
