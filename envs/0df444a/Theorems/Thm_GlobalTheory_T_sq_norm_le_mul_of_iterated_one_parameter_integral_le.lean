-- Prove2me | Theorems.Thm_GlobalTheory_T_sq_norm_le_mul_of_iterated_one_parameter_integral_le
-- name    : GlobalTheory.T.sq_norm_le_mul_of_iterated_one_parameter_integral_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:59:05.929498+00:00
-- url     : https://prove2.me/theorems/73ab40a0-9bc3-4a7f-abec-bae5e5038168
-- title:
--   T: sq norm le mul of iterated one parameter integral le
-- statement:
--   The T construction uses the sq norm le mul of iterated one parameter integral le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SobolevIteratedOneParameterSubgroupsWordsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SobolevIteratedOneParameterSubgroupsWordsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SobolevIteratedOneParameterSubgroupsWords
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SobolevIteratedOneParameterSubgroupsWordsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sq_norm_le_mul_of_iterated_one_parameter_integral_le : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : ℕ) (c : Fin N → ℝ → G) (s : ℝ), 0 < s → (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : List (Fin N) → G → ℂ), (∀ l, Continuous (F l)) → (∀ l i x, HasDerivAt (fun t => F l (x * c i t)) (F (i :: l) x) 0) → ∀ (y : G) (M : ℝ), (∀ l : List (Fin N), l.length ≤ N → ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), ‖F l (y * (List.ofFn fun i => c i (t i)).prod)‖ ^ 2 ≤ M) → ‖F [] y‖ ^ 2 ≤ C * M := by sorry
