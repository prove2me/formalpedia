-- Prove2me | Theorems.Thm_GlobalTheory_unitary_stabiliser_orthogonal_summand
-- name    : GlobalTheory.unitary_stabiliser_orthogonal_summand
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:30:25.525684+00:00
-- url     : https://prove2.me/theorems/ca106ab7-9208-434d-8f92-661dd5e99a68
-- title:
--   Global Theory: unitary stabiliser orthogonal summand
-- statement:
--   The Global Theory construction uses the unitary stabiliser orthogonal summand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryStabiliserOrthogonalSummand.lean#L12-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/UnitaryStabiliserOrthogonalSummand.lean#L12-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_UnitaryStabiliserOrthogonalSummand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.unitary_stabiliser_orthogonal_summand :
    ∀ (R : Type) [CommRing R] (s : R →+* R) (N ι κ : Type) [Fintype N] [DecidableEq N] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (J : Matrix N N R) (G : Matrix ι ι R) (G' : Matrix κ κ R) (Q : Matrix N (ι ⊕ κ) R) (Qi : Matrix (ι ⊕ κ) N R), Q * Qi = 1 → Qi * Q = 1 → (Q.map s)ᵀ * J * Q = Matrix.fromBlocks G 0 0 G' → IsUnit G'.det → (∀ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G → ((Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi).map s)ᵀ * J * (Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi) = J) ∧ ∀ h : Matrix N N R, (h.map s)ᵀ * J * h = J → (∀ b : κ, h *ᵥ (fun i => Q i (Sum.inr b)) = fun i => Q i (Sum.inr b)) → ∃ y : Matrix ι ι R, (y.map s)ᵀ * G * y = G ∧ h = Q * Matrix.fromBlocks y 0 0 (1 : Matrix κ κ R) * Qi := by sorry
