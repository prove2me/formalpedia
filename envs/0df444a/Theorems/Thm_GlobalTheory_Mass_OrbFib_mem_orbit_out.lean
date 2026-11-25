-- Prove2me | Theorems.Thm_GlobalTheory_Mass_OrbFib_mem_orbit_out
-- name    : GlobalTheory.Mass.OrbFib.mem_orbit_out
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:20:32.234867+00:00
-- url     : https://prove2.me/theorems/f50fe3a5-1dfc-42b2-bc79-09ee7b2eae7e
-- title:
--   Orb Fib: mem orbit out
-- statement:
--   The Orb Fib construction uses the mem orbit out property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L69-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/OrbitStabilizerMassEqWeightedSumFibres.lean#L69-L75

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

theorem GlobalTheory.Mass.OrbFib.mem_orbit_out (q : MulAction.orbitRel.Quotient G α) (x : α) :
    x ∈ MulAction.orbit G (Quotient.out q) ↔ (Quotient.mk (MulAction.orbitRel G α) x) = q := by sorry
