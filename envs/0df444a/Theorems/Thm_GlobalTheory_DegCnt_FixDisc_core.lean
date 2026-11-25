-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FixDisc_core
-- name    : GlobalTheory.DegCnt.FixDisc.core
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:26.288687+00:00
-- url     : https://prove2.me/theorems/17409a51-dfaf-49bb-afeb-afe6f9cf348a
-- title:
--   Fix Disc: core
-- statement:
--   The Fix Disc construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L325-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L325-L364

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
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.FixDisc.core {H : HermSpace K V} (hK : IsCMUnram K) (hP : PD H.B.flip) {η : V ≃ₗ[K] V}
    (hη : ∀ x y, H.B (η x) (η y) = H.B x y) {g : ℕ} (hg : 0 < g) {A D : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) (hD : Submodule.IsLattice K D) (hle : D ≤ Formalism.HermitianLatticesTheory.dual H.B.flip A)
    (hfix : ∀ t ∈ fixSp η, t ∈ D → t ∈ A)
    (hpair : ∀ y ∈ D, (g : K)⁻¹ • (y - η y) ∈ Formalism.HermitianLatticesTheory.dual H.B.flip A) :
    (discN (hRes H.B.flip (fixSp η)) (latIn (fixSp η) A) : ℝ) ≤
      (2 / (g : ℝ)) ^ (2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K) *
        idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) D := by sorry
