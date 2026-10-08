-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_rat_den_le_abs_sub_lt_one
-- name    : OAI.PiExponent.finite_rat_den_le_abs_sub_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-07T07:00:52.874546+00:00
-- url     : https://prove2.me/theorems/6a1e361b-a076-4905-946e-fcbbffca3403
-- title:
--   Bounded-denominator rational approximations form a finite set
-- statement:
--   For every real number $x$ and natural number $N$, the set of rational numbers whose reduced denominator is at most $N$ and whose distance from $x$ is less than $1$ is finite:
--   $$\{r\in\mathbb Q:r.\mathrm{den}\le N,\ |x-r|<1\}.\mathrm{Finite}.$$
--   This supplies the finite exceptional set needed when replacing eventual denominator bounds by finiteness statements about rational approximations.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/Exponent.lean#L28-L55

import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_OAI_PiExponent_ApproximationDefinitions

open OAI.PiExponent

theorem OAI.PiExponent.finite_rat_den_le_abs_sub_lt_one (x : ℝ) (N : ℕ) :
    {r : ℚ | r.den ≤ N ∧ |x - (r : ℝ)| < 1}.Finite := by sorry
