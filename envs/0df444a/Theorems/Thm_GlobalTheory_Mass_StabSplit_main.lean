-- Prove2me | Theorems.Thm_GlobalTheory_Mass_StabSplit_main
-- name    : GlobalTheory.Mass.StabSplit.main
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:34:34.487232+00:00
-- url     : https://prove2.me/theorems/984aae36-2ce3-54ce-9ede-657c0113eaee
-- title:
--   Stab Split: main
-- statement:
--   The Stab Split construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean#L182-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/DefiniteUnitaryStabilizerSubspaceProd.lean#L182-L252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteUnitaryStabilizerSubspaceProd
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.StabSplit
open NumberField Matrix
open scoped ENNReal Classical

theorem GlobalTheory.Mass.StabSplit.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ U : Submodule K V,
    ∃ φ : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) U ≃*
      _root_.Formalism.HermitianLatticesTheory.isom (_root_.GlobalTheory.Mass.hRes h U) ×
        _root_.Formalism.HermitianLatticesTheory.isom (_root_.GlobalTheory.Mass.hRes h (_root_.GlobalTheory.Mass.perp h U)),
    ∀ (γ : MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) U) (L : Submodule (𝓞 K) V),
      _root_.GlobalTheory.Mass.latIn U (γ • L) = (φ γ).1 • _root_.GlobalTheory.Mass.latIn U L ∧
      _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) (γ • L) =
        (φ γ).2 • _root_.GlobalTheory.Mass.latIn (_root_.GlobalTheory.Mass.perp h U) L := by sorry
