-- Prove2me | Theorems.Thm_GeneralCK_noiseKernel_sum
-- name    : GeneralCK.noiseKernel_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T19:31:34.306981+00:00
-- url     : https://prove2.me/theorems/cb8d69aa-3979-4dbb-85c5-3d82af21d89e
-- title:
--   Normalization of the binary symmetric channel kernel
-- statement:
--   Let $n\in\mathbb N$, $x\in\{0,1\}^n$, and $p\in\mathbb R$. Define $K_p(x,y)$ as the product over coordinates of $1-p$ when the coordinates agree and $p$ otherwise. Then $$\sum_{y\in\{0,1\}^n}K_p(x,y)=1.$$ The identity holds algebraically for every real $p$, including in dimension zero. For $0\le p\le1$, it states that the independent bit-flip channel has total output probability one. This is a foundational normalization used in the Courtade–Kumar formalization.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Distribution.lean#L13-L21

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_GeneralCK_statement

open scoped BigOperators

open GeneralCK

theorem GeneralCK.noiseKernel_sum {n : ℕ} (p : ℝ) (x : Cube n) :
    ∑ y, noiseKernel p x y = 1 := by sorry
