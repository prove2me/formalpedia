-- Prove2me | Theorems.Thm_GlobalTheory_MassOrth_main
-- name    : GlobalTheory.MassOrth.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:33:14.195677+00:00
-- url     : https://prove2.me/theorems/5d8b7f97-5cb2-49a2-a536-480c30796a1c
-- title:
--   Mass Orth: main
-- statement:
--   The Mass Orth construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L289-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsMaxVector.lean#L289-L328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
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
open GlobalTheory GlobalTheory.MassOrth

theorem GlobalTheory.MassOrth.main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ b : Module.Basis (Fin (Module.finrank K V)) K V, (∀ i l, i ≠ l → h (b i) (b l) = 0) ∧ ∀ x, x ∈ loc (K := K) P M ↔ ∀ i, b.repr x i ∈ locR (K := K) P := by sorry
