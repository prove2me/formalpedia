-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_window19
-- name    : HlawkaSchatten.DiagonalCutoff16.real_three_window19
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T01:12:37.487761+00:00
-- url     : https://prove2.me/theorems/00bf80d7-b0e9-4939-88e6-89a6c697dc07
-- title:
--   Sharp real three-dimensional Hlawka bound for 71/4 <= p <= 18
-- statement:
--   For every real exponent $71/4\le p\le 18$ and every three vectors $x,y,z\in\mathbb R^3$, let $\|\cdot\|_p$ be the usual coordinate $\ell^p$ norm and set
--   $$S=\|x\|_p+\|y\|_p+\|z\|_p,\quad T=\|x+y+z\|_p,$$
--   $$P=\|x+y\|_p+\|x+z\|_p+\|y+z\|_p.$$
--   Let $K_p$ be the cyclic comparison constant
--   $$K_p=\sup_{1/2\le t\le2}\frac{3(t^p+2)^{1/p}-3^{1/p}|2-t|}{6(t^p+2)^{1/p}-3(2|1-t|^p+2^p)^{1/p}}.$$
--   Then
--   $$S-T\le K_p(2S-P).$$
--   This is one complete exponent window in the cutoff-16 extension. It covers arbitrary real triples in dimension three, including zero vectors and unequal singleton norms. Generic dimension reduction and complex transfer can be applied separately. This theorem alone makes no assertion about exponents outside its stated interval.
-- source:
--   Original cutoff-16 extension, 25 October 2026, complete window 19. Extends Sections 3-5 of Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.tex . The normalization, contraction, Hessian and averaging arguments reuse attributed Apache-2.0 Prove2Me proofs; the total-norm barrier and the numerical constants for the present exponent range are new. All reused proofs and new finite comparisons are included in the Lean submission.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff16.real_three_window19 :
    ∀ p : ℝ, (71/4 : ℝ) ≤ p → p ≤ (18 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
