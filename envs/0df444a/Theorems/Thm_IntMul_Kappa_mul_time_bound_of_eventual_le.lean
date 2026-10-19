-- Prove2me | Theorems.Thm_IntMul_Kappa_mul_time_bound_of_eventual_le
-- name    : IntMul.Kappa.mul_time_bound_of_eventual_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T17:45:32.303155+00:00
-- url     : https://prove2.me/theorems/e7c09682-9aa9-4742-946a-c9831f28349d
-- title:
--   Eventual running-time majorisation for multitape integer multiplication
-- statement:
--   A single fixed multiplication Turing machine with an eventual upper time bound g also satisfies the eventual upper time bound h whenever g(n) ≤ h(n) for all sufficiently large positive n. The same machine works for every input length. This is the reusable complexity-bound bridge needed to derive OpenAI Theorem 1 (κ = 2^-182) from any stronger verified positive-κ bound; it does not assert any such stronger bound itself.
-- source:
--   Derived from the exact definitions of IntMul.MulTimeBound and IntMul.MultipliesAt in Definitions.Def_IntMul_MultitapeModel; contributes to mission e901a985-a077-435a-bd78-2df1c12fb4f3.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

theorem IntMul.Kappa.mul_time_bound_of_eventual_le
    {g h : ℕ → ℝ}
    (hgh : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → g n ≤ h n)
    (hg : IntMul.MulTimeBound g) : IntMul.MulTimeBound h := by sorry
