-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_real_three_w000_s000_000
-- name    : HlawkaSchatten.DiagonalCutoff16.real_three_w000_s000_000
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T23:48:10.190911+00:00
-- url     : https://prove2.me/theorems/dc107923-e892-4e6f-9281-f1b222fdd7db
-- title:
--   Sharp real three-dimensional Hlawka bound for 16 <= p <= 8193/512
-- statement:
--   For every real exponent $16\le p\le 8193/512$, the sharp cyclic Hlawka constant $K_p$ satisfies
--   $$\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p\le K_p\bigl(2\|x\|_p+2\|y\|_p+2\|z\|_p-\|x+y\|_p-\|x+z\|_p-\|y+z\|_p\bigr)$$
--   for all $x,y,z\in\mathbb R^3$. Here $K_p$ is the original cyclicConstant defined in the parent cutoff-16 mission. This complete small interval is separated from the larger interval solely to fit the platform verification time limit. It makes no claim about other exponents.
-- source:
--   Original cutoff-16 extension, 25 October 2026, complete window 00. Extends Sections 3-5 of Yuxuan Xu, A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.tex . The normalization, contraction, Hessian and averaging arguments reuse attributed Apache-2.0 Prove2Me proofs; the total-norm barrier and the numerical constants for the present exponent range are new. All reused proofs and new finite comparisons are included in the Lean submission. Subinterval 0 through 0, separated to fit the platform 300-second verification limit.

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff16.real_three_w000_s000_000 :
    ∀ p : ℝ, (16 : ℝ) ≤ p → p ≤ (8193/512 : ℝ) →
      HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by sorry
