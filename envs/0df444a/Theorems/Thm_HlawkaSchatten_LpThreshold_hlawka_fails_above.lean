-- Prove2me | Theorems.Thm_HlawkaSchatten_LpThreshold_hlawka_fails_above
-- name    : HlawkaSchatten.LpThreshold.hlawka_fails_above
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T02:18:43.200983+00:00
-- url     : https://prove2.me/theorems/0dd86d5d-13e9-41f1-b1d9-7291d450458b
-- title:
--   Hlawka's inequality fails in $\ell_p(3)$ for $p>\log 3/\log(3/2)$
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
--   **Statement.** For every real $p>p_W$, Hlawka's inequality fails in $\ell_p(3)=(\mathbb R^3,\|\cdot\|_p)$.
--
--   The witness is the triple $x=(-1,1,1)$, $y=(1,-1,1)$, $z=(1,1,-1)$. Its pair sums have norm $2$, while $x$, $y$, $z$ and $x+y+z$ have norm $3^{1/p}$. The inequality therefore reads $6\le 4\cdot 3^{1/p}$, which is false exactly when $3^{1/p}<3/2$, that is, when $p>p_W$.
-- source:
--   D.-Ș. Marinescu and C. P. Niculescu, A survey of the Hornich-Hlawka inequality, arXiv:2407.03278v1 (2024), Section 3, remark following Theorem 2 (the triple x=(-1,1,1), y=(1,-1,1), z=(1,1,-1)) and Problem 1

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.LpThreshold.hlawka_fails_above :
    ∀ p : ℝ, Real.log 3 / Real.log (3 / 2) < p →
      ¬ HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) 1 := by sorry
