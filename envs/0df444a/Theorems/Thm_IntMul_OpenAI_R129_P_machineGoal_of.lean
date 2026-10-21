-- Prove2me | Theorems.Thm_IntMul_OpenAI_R129_P_machineGoal_of
-- name    : IntMul.OpenAI.R129.P.machineGoal_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-20T13:27:59.214332+00:00
-- url     : https://prove2.me/theorems/0508e194-c90e-4fea-81b4-8f2c2ffac8de
-- title:
--   From a polylog-slack machine bound to the R129 machine statement
-- statement:
--   If a correct multitape machine $M$ runs, for all $n \ge \max(n_0, n_1)$, in time at most $$C_0\left(V(n)\,\mathrm{Ncost}(n)\,(\log(6\lg n) + 1)^A + n\right)$$ with the `same-network-129` parameters, then it satisfies the statement of `IntMul.OpenAI.R129.machine` (`MachineGoal`), with slack factor $(\log \lg n + 1)^A$: since $\log 6 \le 5$, $\log(6x) + 1 \le 6(\log x + 1)$ for $x \ge 1$, so the constant becomes $6^A C_0$.
-- source:
--   OpenAI, Integer multiplication below n log n (preprint, 23 Sep 2026), https://github.com/openai/math/tree/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Integer-multiplication-below-n-log-n-September-23-2026, §8 and §9 with the same-network-129 constants of https://github.com/CrocSwap/integer-mult-bounds. Replaces `NLogN.KFM.kappaBound_of_machine_polylog` at the top of the machine development.

import Mathlib
import Definitions.Def_IntMul_OpenAI_R129_P_Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Real

theorem IntMul.OpenAI.R129.P.machineGoal_of (M : IntMul.MultitapeTM)
    (hcorr : ∀ n : ℕ, 1 ≤ n → ∃ T : ℝ, IntMul.MultipliesAt M n T)
    (n₁ : ℕ) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (A : ℕ)
    (htime : ∀ n, IntMul.OpenAI.Glue.n0 ≤ n → n₁ ≤ n → IntMul.MultipliesAt M n
      (C₀ * (IntMul.OpenAI.Glue.VP n * IntMul.OpenAI.R129.Ncost (6 * (IntMul.lg n : ℝ))
        (IntMul.OpenAI.R129.dP n) (IntMul.OpenAI.R129.KP n) (IntMul.OpenAI.R129.ℓP n)
        (IntMul.OpenAI.R129.αP n) * (Real.log (6 * (IntMul.lg n : ℝ)) + 1) ^ A + n))) :
    IntMul.OpenAI.R129.P.MachineGoal := by sorry
