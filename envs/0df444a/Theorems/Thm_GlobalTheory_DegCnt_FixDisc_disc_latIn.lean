-- Prove2me | Theorems.Thm_GlobalTheory_DegCnt_FixDisc_disc_latIn
-- name    : GlobalTheory.DegCnt.FixDisc.disc_latIn
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:18:34.293937+00:00
-- url     : https://prove2.me/theorems/fd49dad8-c79e-48ec-8c7f-c39d69afb8c2
-- title:
--   Fix Disc: disc lat In
-- statement:
--   The Fix Disc construction uses the disc lat In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L250-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DiscriminantOrderCommonFixedLatticeEmbeddedData.lean#L250-L279

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

theorem GlobalTheory.DegCnt.FixDisc.disc_latIn {H : HermSpace K V} (hP : PD H.B.flip) {U : Submodule K V} (p : V →ₗ[K] U)
    (p1 : ∀ t : U, p t = t) (p2 : ∀ (x : V) (t : U), H.B t (p x) = H.B t x) {A : Submodule (𝓞 K) V}
    (hA : Submodule.IsLattice K A) :
    discN (hRes H.B.flip U) (latIn U A) =
      idxN (Formalism.HermitianLatticesTheory.dual H.B.flip A) ((latIn U A).comap (p.restrictScalars (𝓞 K))) := by sorry
