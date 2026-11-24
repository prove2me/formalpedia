-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_compactSupport_hasSum_lattice_translates
-- name    : GlobalTheory.exists_smooth_compactSupport_hasSum_lattice_translates
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:06.715211+00:00
-- url     : https://prove2.me/theorems/7e5bf4aa-37a9-4179-a53e-3e36daae3985
-- title:
--   Global Theory: exists smooth compact Support has Sum lattice translates
-- statement:
--   The Global Theory construction uses the exists smooth compact Support has Sum lattice translates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothCompactSupportHasSumLatticeTranslate.lean#L24-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothCompactSupportHasSumLatticeTranslate.lean#L24-L96

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

theorem GlobalTheory.exists_smooth_compactSupport_hasSum_lattice_translates :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L], ∃ η : V → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ ∀ y, HasSum (fun l : L => η (y + l)) 1 := by sorry
