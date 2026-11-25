-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_standard_basis_extension_det_ne_zero
-- name    : GlobalTheory.T.exists_standard_basis_extension_det_ne_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:30:54.418045+00:00
-- url     : https://prove2.me/theorems/9548fd60-4920-52df-8fb6-d4ab95c60eaf
-- title:
--   T: exists standard basis extension det ne zero
-- statement:
--   The T construction uses the exists standard basis extension det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStandardBasisExtensionDetNeZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsStandardBasisExtensionDetNeZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStandardBasisExtensionDetNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsStandardBasisExtensionDetNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_standard_basis_extension_det_ne_zero : ∀ {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K), LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧ (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by sorry
