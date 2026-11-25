-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FixDisc_exists_proj_aut
-- name    : GlobalTheory.DegCnt.FixDisc.exists_proj_aut
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:03.856666+00:00
-- url     : https://prove2.me/theorems/23507f6d-577a-5f5e-8225-7f8792cee6e8
-- title:
--   Fix Disc: exists proj aut
-- statement:
--   The Fix Disc construction uses the exists proj aut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L172-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L172-L245

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
omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.DegCnt.FixDisc.exists_proj_aut {H : HermSpace K V} (hK : IsCMUnram K) (hP : PD H.B.flip) {η : V ≃ₗ[K] V}
    (hη : ∀ x y, H.B (η x) (η y) = H.B x y) {g : ℕ} (hg : 0 < g) :
    ∃ (p : V →ₗ[K] fixSp η) (F : V ≃ₗ[K] V), (∀ t : fixSp η, p t = t) ∧
      (∀ (x : V) (t : fixSp η), H.B t (p x) = H.B t x) ∧ (∀ x, p (x - η x) = 0) ∧
      (∀ x, F x = p x + (g : K)⁻¹ • (x - η x)) ∧
      ((|Algebra.norm ℚ (LinearMap.det (F : V →ₗ[K] V))| : ℚ) : ℝ) ≤
        (2 / (g : ℝ)) ^ (2 * (Module.finrank K V - Module.finrank K (fixSp η)) * fDeg K) := by sorry
