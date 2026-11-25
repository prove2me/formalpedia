-- Prove2me | Theorems.Thm_GlobalTheory_Mass_OrbFib_encard_orbits
-- name    : GlobalTheory.Mass.OrbFib.encard_orbits
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:52.160902+00:00
-- url     : https://prove2.me/theorems/3311a55b-0475-4b9f-8888-4ec789e9373b
-- title:
--   Orb Fib: encard orbits
-- statement:
--   The Orb Fib construction uses the encard orbits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L80-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L80-L122

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
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.OrbFib
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]
open NumberField Matrix
open scoped ENNReal Classical
variable {G α β : Type} [Group G] [MulAction G α] [MulAction G β]

theorem GlobalTheory.Mass.OrbFib.encard_orbits (X : Set α) (hX : _root_.GlobalTheory.Mass.Stable G X)
    (S : Set α) :
    (((X ∩ S).encard : ℕ∞) : ℝ≥0∞) =
      ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
        (((MulAction.orbit G (Quotient.out q.1) ∩ S).encard : ℕ∞) : ℝ≥0∞) := by sorry
