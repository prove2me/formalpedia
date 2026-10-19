-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff21_cyclicConstant_upper21
-- name    : HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T09:02:27.849994+00:00
-- url     : https://prove2.me/theorems/6a6590b3-eb58-4251-9cc2-59e3721f34f5
-- title:
--   Cyclic Hlawka constant at most p/2 throughout [21,32]
-- statement:
--   Let $p$ be any real exponent with $21\le p\le32$. Define
--
--   $$A_p(t)=(t^p+2)^{1/p},\qquad B_p(t)=(2|1-t|^p+2^p)^{1/p},$$
--   $$R_p(t)=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},\qquad K_p=\sup_{1/2\le t\le2}R_p(t).$$
--
--   Then $K_p\le p/2$. The exponent ranges over the entire real interval. This is the upper-bound component of both scalar-window milestones in the source paper.
-- source:
--   Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1 (2026), https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/main/paper/main.pdf . Section 2, equation (7), upper-bound component; elementary analytic proof in formalization/Hlawka21/CyclicUpper.lean.

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Analysis.Complex.ExponentialBounds
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff21.cyclicConstant_upper21 {p : ℝ} (hp : 21 ≤ p) (hp32 : p ≤ 32) :
    cyclicConstant p ≤ p/2 := by sorry
