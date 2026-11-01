-- Prove2me | Theorems.Thm_OAI_JointDickman_squarefree_integer_rational_polylog_sum_bound_jd
-- name    : OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:29:59.696864+00:00
-- url     : https://prove2.me/theorems/f090d1e2-3c4c-4a82-90d8-f7416d49a95c
-- title:
--   OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound` of [lean/OAI/NumberTheory/JointDickman/Amplification/IntegerRationalSum.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/IntegerRationalSum.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset`, `open scoped ComplexConjugate`):
--
--   ```lean
--   theorem squarefree_integer_rational_polylog_sum_bound_jd : ∃ C : ℝ, 0 < C ∧
--       ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
--       (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ),
--       2 ≤ B → B^20 ≤ N → 0 < q → u.natAbs.Coprime q → Real.log N ≤ 3*(B:ℝ) →
--       (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
--       ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*((u:ℝ)/q))‖ ≤
--         C*N*(1+Real.log B)/Real.log N
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.additivePhase` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.weighted_geometric_period_model_vanishing_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/IntegerRationalSum.lean (declaration OAI.JointDickman.squarefree_integer_rational_polylog_sum_bound)

import Mathlib
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset
open scoped ComplexConjugate

theorem squarefree_integer_rational_polylog_sum_bound_jd : ∃ C : ℝ, 0 < C ∧
    ∀ (f : ArithmeticFunction ℝ), f.IsMultiplicative → (∀ n, |f n| ≤ 1) →
    (∀ n, ¬Squarefree n → f n=0) → ∀ (N B q : ℕ) (u : ℤ),
    2 ≤ B → B^20 ≤ N → 0 < q → u.natAbs.Coprime q → Real.log N ≤ 3*(B:ℝ) →
    (B:ℝ)^12 ≤ q → (q:ℝ) ≤ N/(B:ℝ)^8 →
    ‖∑ n ∈ Ioc 0 N, (f n:ℂ)*additivePhase ((n:ℝ)*((u:ℝ)/q))‖ ≤
      C*N*(1+Real.log B)/Real.log N := by
  sorry

end JointDickman

end OAI
end
