-- Prove2me | Theorems.Thm_GlobalTheory_T_real_compact_partition_unity
-- name    : GlobalTheory.T.real_compact_partition_unity
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:36:35.0637+00:00
-- url     : https://prove2.me/theorems/bceba7ac-26d1-40ff-9b8d-811eca296dac
-- title:
--   T: real compact partition unity
-- statement:
--   The T construction uses the real compact partition unity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnityStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RealCompactPartitionUnityStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnity
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RealCompactPartitionUnityStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.real_compact_partition_unity : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    ∃ ψ : SchwartzMap V ℂ, HasCompactSupport (ψ : V → ℂ) ∧ (∀ x, starRingEnd ℂ (ψ x) = ψ x) ∧
      ∃ v : (Fin (Module.finrank ℝ V) → ℤ) → V, (∀ x, HasSum (fun j => ψ (x - v j)) 1) ∧
        (∀ R : ℝ, {j | ‖v j‖ ≤ R}.Finite) ∧ ∃ M : ℕ, Summable (fun j => ((1 + ‖v j‖) ^ M)⁻¹) := by sorry
