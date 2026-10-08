-- Prove2me | Theorems.Thm_HornichHlawka_MarinescuNiculescu_problem1_real
-- name    : HornichHlawka.MarinescuNiculescu.problem1_real
-- status  : Open
-- author  : @moona3k
-- created : 2026-10-05T02:18:58.158103+00:00
-- url     : https://prove2.me/theorems/ded626ba-191e-4e2d-af4e-7b0c8caac2ba
-- title:
--   Marinescu–Niculescu Problem 1 (real exponents): no $\ell_p(3)$ with $p>2$ is Hornich–Hlawka
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
--   **Statement (as posed).** Problem 1 of Marinescu–Niculescu asks to prove that none of the spaces $\ell_p(3)$ with $p\in(2,\infty]$ is Hornich–Hlawka. This entry formalises the finite real exponents $p\in(2,\infty)$: for every real $p>2$, Hlawka's inequality fails in $\ell_p(3)$. The case $p=\infty$ is already settled by the triple above.
--
--   The survey establishes the range $p>p_W$. The range $2<p\le p_W$ is what the problem leaves open. A disproof needs a single exponent in $(2,p_W]$ at which $\ell_p(3)$ is Hornich–Hlawka, for example via `hlawka_holds_five_halves`.
-- source:
--   D.-Ș. Marinescu and C. P. Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1 (2024), Section 3, remark following Theorem 2 (the triple x=(-1,1,1), y=(1,-1,1), z=(1,1,-1)) and Problem 1

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HornichHlawka.MarinescuNiculescu.problem1_real :
    ∀ p : ℝ, 2 < p → ¬ HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) 1 := by sorry
