-- Prove2me | Theorems.Thm_GlobalTheory_Mass_OrbFib_key
-- name    : GlobalTheory.Mass.OrbFib.key
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:32:00.728923+00:00
-- url     : https://prove2.me/theorems/4faea023-98d6-4603-bdf0-658b5b2cc95c
-- title:
--   Orb Fib: key
-- statement:
--   The Orb Fib construction uses the key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L19-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L19-L64

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

theorem GlobalTheory.Mass.OrbFib.key (π : α → β)
    (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : α) (k : G) :
    ((ENat.card (MulAction.stabilizer G (k • π x)) : ℕ∞) : ℝ≥0∞) =
      (((MulAction.orbit G x ∩ π ⁻¹' {k • π x}).encard : ℕ∞) : ℝ≥0∞) *
        ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞) := by sorry
