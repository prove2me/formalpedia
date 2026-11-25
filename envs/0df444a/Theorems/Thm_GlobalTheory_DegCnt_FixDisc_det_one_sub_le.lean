-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FixDisc_det_one_sub_le
-- name    : GlobalTheory.DegCnt.FixDisc.det_one_sub_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:16:30.472578+00:00
-- url     : https://prove2.me/theorems/04ea9dd5-e1ae-5492-b047-3bcf46518999
-- title:
--   Fix Disc: det one sub le
-- statement:
--   The Fix Disc construction uses the det one sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L117-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L117-L153

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FlagPairDefinitePartLattice
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_NormalFormDualOrthogonalLast
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DiscriminantOrderCommonFixedLatticeEmbeddedData
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
open GlobalTheory GlobalTheory.DegCnt GlobalTheory.DegCnt.FixDisc
open GlobalTheory.Mass GlobalTheory.Mass.DiscOrder Formalism.HermitianLatticesTheory

theorem GlobalTheory.DegCnt.FixDisc.det_one_sub_le {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (σ : K →+* ℂ) (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U)
    (hσ : ∀ x : K, σ (star x) = star (σ x)) (herm : ∀ x y : U, star (h x y) = h y x)
    (hpos : ∀ w : U, w ≠ 0 → 0 < (σ (h w w)).re) (hη : ∀ x y : U, h (η x) (η y) = h x y) :
    ‖σ (LinearMap.det (LinearMap.id - η))‖ ≤ 2 ^ Module.finrank K U := by sorry
