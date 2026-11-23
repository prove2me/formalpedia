-- Prove2me | Theorems.Thm_GlobalTheory_exists_radius_lattice_translate_norm_le
-- name    : GlobalTheory.exists_radius_lattice_translate_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:19:09.25082+00:00
-- url     : https://prove2.me/theorems/b5c99e29-8946-46bc-93a0-178f4b6e51c2
-- title:
--   Global Theory: exists radius lattice translate norm le
-- statement:
--   The Global Theory construction uses the exists radius lattice translate norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothCompactSupportHasSumLatticeTranslate.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothCompactSupportHasSumLatticeTranslate.lean#L8-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmoothPeriodicPartitionOfUnity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory

theorem GlobalTheory.exists_radius_lattice_translate_norm_le (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]
    [IsZLattice ℝ L] : ∃ R : ℝ, 0 < R ∧ ∀ y : V, ∃ l : L, ‖y + l‖ ≤ R := by sorry
