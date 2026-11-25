-- Prove2me | Theorems.Thm_GlobalTheory_Mass_SplitOver_exists_unique_over
-- name    : GlobalTheory.Mass.SplitOver.exists_unique_over
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T05:01:33.146203+00:00
-- url     : https://prove2.me/theorems/68e71a3c-f246-4bd0-90cb-e125329619c8
-- title:
--   Split Over: exists unique over
-- statement:
--   The Split Over construction uses the exists unique over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnimodularOverlatticeCyclicSplitDiscrimina.lean#L70-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnimodularOverlatticeCyclicSplitDiscrimina.lean#L70-L127

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

theorem GlobalTheory.Mass.SplitOver.exists_unique_over (P : Ideal (𝓞 K)) (hc : IsCoprime P (conjIdeal (K := K) P))
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L)
    (e : Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P * conjIdeal (K := K) P))) :
    ∃! M : Submodule (𝓞 K) V, Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
      Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) := by sorry
