-- Prove2me | Theorems.Thm_GlobalTheory_rightInv_lower_transvection
-- name    : GlobalTheory.rightInv_lower_transvection
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:17:15.685806+00:00
-- url     : https://prove2.me/theorems/026c6fce-1c25-43e1-93e1-a0c6a73f34fc
-- title:
--   Global Theory: right Inv lower transvection
-- statement:
--   The Global Theory construction uses the right Inv lower transvection property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L104-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightInvariantGLOfUpperTriangularRightInvariant.lean#L104-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightInvariantGLOfUpperTriangularRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Polynomial
open GlobalTheory
variable {k : Type} [Field k] [Infinite k] {m : ℕ}

theorem GlobalTheory.rightInv_lower_transvection (ψ Φ : Matrix (Fin m) (Fin m) k → k) (r : k → k)
    (hΦ : ∀ A₀ D : Matrix (Fin m) (Fin m) k, ∃ p : Polynomial k, ∀ x : k, Φ (A₀ + x • D) = p.eval x)
    (hψ : ∀ A : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → ψ A = r A.det * Φ A)
    (hT : ∀ A T : Matrix (Fin m) (Fin m) k, A.det ≠ 0 → T.det ≠ 0 → T.BlockTriangular id →
      ψ (A * T) = ψ A)
    (A : Matrix (Fin m) (Fin m) k) (hA : A.det ≠ 0) {i j : Fin m} (hji : j < i) (x : k) :
    ψ (A * transvection i j x) = ψ A := by sorry
