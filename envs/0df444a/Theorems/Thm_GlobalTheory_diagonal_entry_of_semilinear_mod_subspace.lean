-- Prove2me | Theorems.Thm_GlobalTheory_diagonal_entry_of_semilinear_mod_subspace
-- name    : GlobalTheory.diagonal_entry_of_semilinear_mod_subspace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:53:03.738964+00:00
-- url     : https://prove2.me/theorems/9a72e519-2469-583e-afe1-63dd2db07a3c
-- title:
--   Global Theory: diagonal entry of semilinear mod subspace
-- statement:
--   The Global Theory construction uses the diagonal entry of semilinear mod subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagonalEntryOfSemilinearModSubspace.lean#L6-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiagonalEntryOfSemilinearModSubspace.lean#L6-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiagonalEntryOfSemilinearModSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
open GlobalTheory

theorem GlobalTheory.diagonal_entry_of_semilinear_mod_subspace : ∀ (F : Type) [Field F] (n : ℕ) (θ : PowerSeries F →+* PowerSeries F) (A : Matrix (Fin n) (Fin n) (PowerSeries F)) (W' W : Submodule (LaurentSeries F) (Fin n → LaurentSeries F)) (f' e' f e : Fin n → PowerSeries F) (w' w : (PowerSeries F)ˣ) (k' k m : ℤ) (d : PowerSeries F) (α : LaurentSeries F), ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ≠ 0 → (∀ y : Fin n → PowerSeries F, (fun a => ((y a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((A.mulVec (fun c => θ (y c)) a : PowerSeries F) : LaurentSeries F)) ∈ W) → (fun a => ((f' a : PowerSeries F) : LaurentSeries F)) - (((w' : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k') • (fun a => ((e' a : PowerSeries F) : LaurentSeries F)) ∈ W' → (fun a => ((f a : PowerSeries F) : LaurentSeries F)) - (((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k) • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∉ W → (fun a => ((A.mulVec (fun c => θ (f' c)) a : PowerSeries F) : LaurentSeries F)) - ((d : PowerSeries F) : LaurentSeries F) • (fun a => ((f a : PowerSeries F) : LaurentSeries F)) ∈ W → (((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m) • (fun a => ((A.mulVec (fun c => θ (e' c)) a : PowerSeries F) : LaurentSeries F)) - α • (fun a => ((e a : PowerSeries F) : LaurentSeries F)) ∈ W → ((θ (w' : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((θ PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k' * α = ((d : PowerSeries F) : LaurentSeries F) * ((w : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ k * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ m := by sorry
