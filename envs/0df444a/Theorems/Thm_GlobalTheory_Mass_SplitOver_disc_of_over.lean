-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SplitOver_disc_of_over
-- name    : GlobalTheory.Mass.SplitOver.disc_of_over
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:55:28.180139+00:00
-- url     : https://prove2.me/theorems/e2e3e214-9218-540d-9aa1-98ade136449f
-- title:
--   Split Over: disc of over
-- statement:
--   The Split Over construction uses the disc of over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnimodularOverlatticeCyclicSplitDiscrimina.lean#L129-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnimodularOverlatticeCyclicSplitDiscrimina.lean#L129-L238

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnimodularOverlatticeCyclicSplitDiscrimina
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SplitOver
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem GlobalTheory.Mass.SplitOver.disc_of_over (P : Ideal (𝓞 K)) (hP0 : P ≠ ⊥) (hc : IsCoprime P (conjIdeal (K := K) P))
    (M L : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (hMu : IsUnimodular h M) (hLM : L ≤ M)
    (e : Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P))) :
    IsIntLat h L ∧
      Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P * conjIdeal (K := K) P)) := by sorry
