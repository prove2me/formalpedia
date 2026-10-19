-- Prove2me | Theorems.Thm_IntMul_Kappa_kappa_bound_of_linear_overhead
-- name    : IntMul.Kappa.kappa_bound_of_linear_overhead
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-16T21:43:29.139997+00:00
-- url     : https://prove2.me/theorems/bd123271-f8e0-43a8-b471-0d2b0d6e79ac
-- title:
--   Absorption of linear tape overhead in multiplication power-saving bounds
-- statement:
--   Suppose κ≤1 and one fixed correct multiplication Turing machine runs in at most c·n·(lg n)^(1−κ)+d·n steps eventually, with c>0 and d≥0. Then that same machine witnesses KappaBound κ, with asymptotic constant c+d. The proof uses lg n≥1 and hence (lg n)^(1−κ)≥1. It certifies that linear input/output conversions, tape rewinds, padding and similar wrapper costs can be absorbed without reducing κ. This is a reusable machine-level complexity bridge, not an algorithm existence claim.
-- source:
--   Elementary complexity accounting for the model IntMul_MultitapeModel, prompted by the exact multitape construction and the need to absorb O(n) tape transformations in OpenAI's 2026 integer-multiplication bound.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
open IntMul

theorem IntMul.Kappa.kappa_bound_of_linear_overhead
    (κ c d : ℝ) (hκ : κ ≤ 1) (hc : 0 < c) (hd : 0 ≤ d)
    (M : IntMul.MultitapeTM)
    (hcorrect : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T)
    (n₀ : ℕ)
    (hcost : ∀ n : ℕ, n₀ ≤ n → 1 ≤ n →
      IntMul.MultipliesAt M n
        (c * ((n : ℝ) * ((IntMul.lg n : ℝ) ^ (1 - κ))) + d * n)) :
    IntMul.KappaBound κ := by sorry
