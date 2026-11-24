-- Prove2me | Theorems.Thm_GlobalTheory_laurent_degeneration
-- name    : GlobalTheory.laurent_degeneration
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:02:08.793194+00:00
-- url     : https://prove2.me/theorems/bf52882f-d56b-40c8-94ff-e1339797442e
-- title:
--   Global Theory: laurent degeneration
-- statement:
--   The Global Theory construction uses the laurent degeneration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentDegenerationFirstOrderKernel.lean#L107-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LaurentDegenerationFirstOrderKernel.lean#L107-L124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LaurentDegenerationFirstOrderKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.laurent_degeneration : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by sorry
