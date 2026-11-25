-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_InnerLat_unimod_transfer
-- name    : GlobalTheory.DegCnt.InnerLat.unimod_transfer
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:30:35.590871+00:00
-- url     : https://prove2.me/theorems/97f94cfe-d412-472d-b202-a6c38d9b4a70
-- title:
--   Inner Lat: unimod transfer
-- statement:
--   The Inner Lat construction uses the unimod transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairInnerLatticesUnimodularPrimitive.lean#L27-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermFramePairInnerLatticesUnimodularPrimitive.lean#L27-L98

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

theorem GlobalTheory.DegCnt.InnerLat.unimod_transfer [FiniteDimensional K V] (H : HermSpace K V) {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ)
    {X U I : Submodule K V} (hX : ∀ x ∈ X, ∀ y ∈ X, H.B x y = 0) (hUX : U ≤ perp H X)
    (h1 : perp H X ≤ U ⊔ X) (h2 : U ⊓ X = I) :
    IsUnimodMod H (rs (𝓞 K) U ⊓ (Λ ⊔ rs (𝓞 K) X)) U I := by sorry
