-- Prove2me | Theorems.Thm_GlobalTheory_newton_recursion_poly_unique
-- name    : GlobalTheory.newton_recursion_poly_unique
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:12:37.520023+00:00
-- url     : https://prove2.me/theorems/917b6573-0aa8-4bc8-b5ad-7cf262d6f07a
-- title:
--   Global Theory: newton recursion poly unique
-- statement:
--   The Global Theory construction uses the newton recursion poly unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUnique.lean#L31-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/NewtonRecursionPolyUnique.lean#L31-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NewtonRecursionPolyUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Polynomial
open GlobalTheory

theorem GlobalTheory.newton_recursion_poly_unique : ∀ (m N : ℕ) (p : ℕ → ℂ) (f r : ℂ[X]), m < N → p 0 = (m : ℂ) + 1 → f.natDegree ≤ m → r.natDegree ≤ m → (∀ u : ℂ, (u - m) ^ (N + 1) * (f.eval (u + 1) - f.eval u) - f.eval u * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * p k = r.eval u) → f = 0 := by sorry
