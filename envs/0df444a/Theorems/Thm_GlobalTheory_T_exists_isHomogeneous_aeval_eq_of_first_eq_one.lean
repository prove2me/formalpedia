-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_isHomogeneous_aeval_eq_of_first_eq_one
-- name    : GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:20.079385+00:00
-- url     : https://prove2.me/theorems/f0e87ffe-8f7b-4916-885e-3277741fe885
-- title:
--   T: exists is Homogeneous aeval eq of first eq one
-- statement:
--   The T construction uses the exists is Homogeneous aeval eq of first eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsHomogeneousDehomogenizeStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIsHomogeneousDehomogenizeStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHomogeneousDehomogenize
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIsHomogeneousDehomogenizeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_isHomogeneous_aeval_eq_of_first_eq_one : ∀ {D : ℕ} (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ), T₀.totalDegree ≤ q → ∃ T : MvPolynomial (Fin (D + 1)) ℤ, T.IsHomogeneous q ∧ ∀ (R : Type) [CommRing R] (a : Fin (D + 1) → R), a 0 = 1 → aeval a T = aeval (fun j => a j.succ) T₀ := by sorry
