-- Prove2me | Theorems.Thm_GlobalTheory_Mass_orbMass_eq_orbSum_fibre
-- name    : GlobalTheory.Mass.orbMass_eq_orbSum_fibre
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:33:40.47344+00:00
-- url     : https://prove2.me/theorems/2327f9db-252b-518e-95dc-58386207929f
-- title:
--   Mass: orb Mass eq orb Sum fibre
-- statement:
--   The Mass construction uses the orb Mass eq orb Sum fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L187-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L187-L208

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrbitStabilizerMassEqWeightedSumFibres
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
open GlobalTheory GlobalTheory.Mass
open NumberField Matrix
open scoped ENNReal Classical

theorem GlobalTheory.Mass.orbMass_eq_orbSum_fibre : ∀ (G α β : Type) [Group G] [MulAction G α]
    [MulAction G β] (X : Set α) (Y : Set β) (π : α → β), (∀ (g : G) x, π (g • x) = g • π x) →
    _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G Y → Set.MapsTo π X Y →
    (∀ y ∈ Y, Finite (MulAction.stabilizer G y)) →
    _root_.GlobalTheory.Mass.orbMass G X =
      _root_.GlobalTheory.Mass.orbSum G Y (fun y => (((X ∩ π ⁻¹' {y}).encard : ℕ∞) : ℝ≥0∞)) := by sorry
