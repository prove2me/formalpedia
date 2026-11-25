-- Prove2me | Theorems.Thm_GlobalTheory_Mass_Glue_main
-- name    : GlobalTheory.Mass.Glue.main
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:39:22.317668+00:00
-- url     : https://prove2.me/theorems/e1acf90a-1be5-432e-a3f9-4ab20181d7cb
-- title:
--   Glue: main
-- statement:
--   The Glue construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedSubspaceComplement.lean#L210-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardHermitianLatticesGluedSubspaceComplement.lean#L210-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LatticeQuotientGensAndIntermediateCount
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardHermitianLatticesGluedSubspaceComplement
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_main

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.Glue
open NumberField Matrix
open scoped ENNReal Classical
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem GlobalTheory.Mass.Glue.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ (U : Submodule K V) (A : Submodule (𝓞 K) U)
    (B : Submodule (𝓞 K) (_root_.GlobalTheory.Mass.perp h U)) (e e' : ℕ),
    _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h U) A →
    _root_.GlobalTheory.Mass.IsIntLat (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B →
    (∃ t : Finset ↥U, t.card ≤ e ∧ _root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h U) A =
      A ⊔ Submodule.span (𝓞 K) (t : Set _)) →
    (∃ t : Finset ↥(_root_.GlobalTheory.Mass.perp h U), t.card ≤ e' ∧
      _root_.Formalism.HermitianLatticesTheory.dual (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B =
        B ⊔ Submodule.span (𝓞 K) (t : Set _)) →
    {L : Submodule (𝓞 K) V | _root_.GlobalTheory.Mass.IsIntLat h L ∧ _root_.GlobalTheory.Mass.latIn U L = A ∧
      _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) L = B}.encard ≤
      (((_root_.GlobalTheory.Mass.discN (_root_.GlobalTheory.Mass.hRes h U) A *
        _root_.GlobalTheory.Mass.discN
          (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)) B) ^ (e + e') : ℕ) : ℕ∞) := by sorry
