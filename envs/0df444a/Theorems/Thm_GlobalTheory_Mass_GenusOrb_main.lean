-- Prove2me | Theorems.Thm_GlobalTheory_Mass_GenusOrb_main
-- name    : GlobalTheory.Mass.GenusOrb.main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:55:48.800508+00:00
-- url     : https://prove2.me/theorems/43ded4f8-85ce-40cc-95e1-6adabeef5ddd
-- title:
--   Genus Orb: main
-- statement:
--   The Genus Orb construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianGenusMassEqOrbitStabilizerMass.lean#L47-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianGenusMassEqOrbitStabilizerMass.lean#L47-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitWeightedStabilizerSumEqSumOrbitReps
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianGenusMassEqOrbitStabilizerMass
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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.GenusOrb
open NumberField Matrix
open scoped ENNReal Classical

theorem GlobalTheory.Mass.GenusOrb.main : ∀ (K V : Type) [Field K] [NumberField K]
    [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), _root_.Formalism.HermitianLatticesTheory.IsCMUnram K → h.IsSymm →
    _root_.GlobalTheory.Mass.PD h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    ENNReal.ofReal (_root_.Formalism.HermitianLatticesTheory.mass h L) = _root_.GlobalTheory.Mass.orbMass (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    0 < _root_.Formalism.HermitianLatticesTheory.mass h L ∧ _root_.GlobalTheory.Mass.Stable (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) ∧
    (∀ M : Submodule (𝓞 K) V, Submodule.IsLattice K M →
      Finite (MulAction.stabilizer (_root_.Formalism.HermitianLatticesTheory.isom h) M)) ∧
    ∀ (s : Finset (Submodule (𝓞 K) V)) (N : Submodule (𝓞 K) V → ℝ≥0∞), _root_.Formalism.ThetaLiftIndependence.IsClassReps h L s →
      (∀ (g : _root_.Formalism.HermitianLatticesTheory.isom h) M, N (g • M) = N M) →
      ∑ M ∈ s, ENNReal.ofReal ((Nat.card (_root_.Formalism.ThetaLiftIndependence.autL h M) : ℝ))⁻¹ * N M =
        _root_.GlobalTheory.Mass.orbSum (_root_.Formalism.HermitianLatticesTheory.isom h) (_root_.Formalism.HermitianLatticesTheory.genus h L) N := by sorry
