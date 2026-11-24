-- Prove2me | Theorems.Thm_GlobalTheory_exists_smooth_homogeneous_hasSum_unit_smul
-- name    : GlobalTheory.exists_smooth_homogeneous_hasSum_unit_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:06.325667+00:00
-- url     : https://prove2.me/theorems/702b4150-de41-412a-a1a2-657d7ccdfcf6
-- title:
--   Global Theory: exists smooth homogeneous has Sum unit smul
-- statement:
--   The Global Theory construction uses the exists smooth homogeneous has Sum unit smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L133-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsSmoothHomogeneousHasSumUnitSmul.lean#L133-L189

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothCompactSupportHasSumLatticeTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
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
open UnitPartition NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem GlobalTheory.exists_smooth_homogeneous_hasSum_unit_smul : ∀ (K : Type) [Field K] [NumberField K], ∃ h : mixedSpace K → ℝ, ContDiffOn ℝ ∞ h {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ (t : ℝ) x, 0 < t → h (t • x) = h x) ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => h (u • x)) 1) ∧ (∀ a b : ℝ, 0 < a → ∃ C : Set (mixedSpace K), IsCompact C ∧ (∀ x ∈ C, mixedEmbedding.norm x ≠ 0) ∧ ∀ x, h x ≠ 0 → a ≤ mixedEmbedding.norm x → mixedEmbedding.norm x ≤ b → x ∈ C) := by sorry
