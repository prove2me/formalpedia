-- Prove2me | Theorems.Thm_HlawkaSchatten_LpThreshold_hlawka_holds_five_halves
-- name    : HlawkaSchatten.LpThreshold.hlawka_holds_five_halves
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-05T02:18:58.995384+00:00
-- url     : https://prove2.me/theorems/38abe59c-a6be-410b-b4e1-6e417794b196
-- title:
--   Hlawka's inequality in $\ell_{5/2}$
-- statement:
--   For a real exponent $p\ge1$ and $v\in\mathbb R^n$ write $\|v\|_p=\big(\sum_i|v_i|^p\big)^{1/p}$ (`lpNorm p`). **Hlawka's inequality** (also called the Hornich–Hlawka inequality) for $\|\cdot\|_p$ asserts that for all $x,y,z\in\mathbb R^n$,
--   $$
--   \|x+y\|_p+\|y+z\|_p+\|z+x\|_p\ \le\ \|x\|_p+\|y\|_p+\|z\|_p+\|x+y+z\|_p .
--   $$
--   In the platform's notation this is `HasHlawkaConstant (lpNorm p) 1`: the triple gap $\|x\|+\|y\|+\|z\|-\|x+y+z\|$ is at most the sum of the three pair gaps $\|x\|+\|y\|-\|x+y\|$. The threshold exponent is
--   $$
--   p_W=\frac{\log 3}{\log(3/2)}\approx 2.7095 ,
--   $$
--   the exponent at which $3^{1/p}=3/2$.
--
--   **Statement (open).** Hlawka's inequality holds in $\ell_{5/2}(n)$ over $\mathbb R$ for every finite dimension $n$.
--
--   This is the single-exponent case $p=5/2\in(2,p_W)$ of `hlawka_holds_below`. A proof would refute the claim of Marinescu–Niculescu Problem 1 that no $\ell_p(3)$ with $p>2$ is Hornich–Hlawka, since it would exhibit one such exponent.
-- source:
--   D.-Ș. Marinescu and C. P. Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1 (2024), Section 3, remark following Theorem 2 (the triple x=(-1,1,1), y=(1,-1,1), z=(1,1,-1)) and Problem 1

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.LpThreshold.hlawka_holds_five_halves :
    ∀ n : ℕ, HasHlawkaConstant (lpNorm (5 / 2) : (Fin n → ℝ) → ℝ) 1 := by sorry
