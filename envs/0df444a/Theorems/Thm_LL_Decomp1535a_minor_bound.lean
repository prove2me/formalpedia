-- Prove2me | Theorems.Thm_LL_Decomp1535a_minor_bound
-- name    : LL_Decomp1535a.minor_bound
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:11:51.618987+00:00
-- url     : https://prove2.me/theorems/cd4e3dd2-f809-44cf-8e8f-11fd8c32a341
-- title:
--   Trivial minor arc bound
-- statement:
--   Let $N$ be a natural number, $M\subseteq\mathbb{R}$ measurable, and $B\ge 0$ real with $|S_N(\alpha)|\le B$ for all $\alpha\in(0,1]\setminus M$. Then $\left\|\int_{(0,1]\setminus M} F_N\right\|\le B\int_0^1 |S_N(\alpha)|^2\,d\alpha$.
-- source:
--   Liu and Wang 2002, p. 174, proof of Theorem 1

import Mathlib
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F

open MeasureTheory

namespace LL_Decomp1535a
theorem minor_bound (N : ℕ) {M : Set ℝ} (hM : MeasurableSet M) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1 \ M, ‖S N α‖ ≤ B) :
    ‖∫ α in Set.Ioc (0 : ℝ) 1 \ M, F N α‖ ≤ B * ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 := by sorry
end LL_Decomp1535a
