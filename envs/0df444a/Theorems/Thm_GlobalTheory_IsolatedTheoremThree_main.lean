-- Prove2me | Theorems.Thm_GlobalTheory_IsolatedTheoremThree_main
-- name    : GlobalTheory.IsolatedTheoremThree.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:21.5653+00:00
-- url     : https://prove2.me/theorems/fff67612-eba7-4f7c-84a9-67b4bbee0f8f
-- title:
--   Isolated Theorem Three: main
-- statement:
--   The Isolated Theorem Three construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ImportsMore.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ImportsMore.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ImportsMore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IsolatedTheoremThree

theorem GlobalTheory.IsolatedTheoremThree.main : (let d1 : (R : Type) → {A : Type} → [inst : CommRing R] → [inst_1 : CommRing A] → [inst_2 : Algebra R A] → (ℕ → A) → ℕ → Submodule R A := @(fun (R : Type) {A : Type} [CommRing R] [CommRing A] [Algebra R A] (γ : ℕ → A) (N : ℕ) ↦ Submodule.span R (γ '' {m : ℕ | m < N})); ∀ {R A : Type} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A], (∀ (n : ℕ), IsUnit (↑(Nat.factorial n) : A)) → ∀ (ξ : R) (γ : ℕ → A), (∀ (n : ℕ), (↑(Nat.factorial n) : A) * γ n = (Algebra.algebraMap R A : R → A) ξ ^ n) → ∀ (N : ℕ), ∀ w ∈ Submodule.span R (Set.range γ), ∃ w₁ ∈ d1 R γ N, (Algebra.algebraMap R A : R → A) ξ ^ N ∣ w - w₁) := by sorry
