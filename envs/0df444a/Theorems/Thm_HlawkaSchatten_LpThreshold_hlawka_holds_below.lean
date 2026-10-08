-- Prove2me | Theorems.Thm_HlawkaSchatten_LpThreshold_hlawka_holds_below
-- name    : HlawkaSchatten.LpThreshold.hlawka_holds_below
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-05T02:18:46.804124+00:00
-- url     : https://prove2.me/theorems/9e0c08c7-583b-41b0-b8a3-57fa9532b2c1
-- title:
--   Hlawka's inequality in $\ell_p$ for $2\le p\le\log 3/\log(3/2)$
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
--   **Statement (open).** For every real $p$ with $2\le p\le p_W$ and every finite dimension $n$, Hlawka's inequality holds in $\ell_p(n)$ over $\mathbb R$.
--
--   Together with the failure for $p>p_W$, this would make $p_W$ the exact threshold for Hlawka's inequality in $\ell_p$. Marinescu and Niculescu ask in their Problem 1 to prove that $\ell_p(3)$ is *not* Hornich–Hlawka for any $p\in(2,\infty]$. This statement asserts the opposite on $(2,p_W]$.
--
--   Numerical evidence: multi-start maximisation of the ratio of triple gap to pair-gap sum over $\mathbb R^3$, with 400 to 1500 starts per exponent, finds a maximum of exactly $1$ for $2<p\le 2.7$ and a strict violation just above $p_W$. By the platform theorem `real_bound_of_fin_three`, the case $n=3$ already implies every $n$.
-- source:
--   D.-Ș. Marinescu and C. P. Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1 (2024), Section 3, remark following Theorem 2 (the triple x=(-1,1,1), y=(1,-1,1), z=(1,1,-1)) and Problem 1

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.LpThreshold.hlawka_holds_below :
    ∀ p : ℝ, 2 ≤ p → p ≤ Real.log 3 / Real.log (3 / 2) → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ) 1 := by sorry
