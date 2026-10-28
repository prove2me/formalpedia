-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_cyclicConstant_upper16
-- name    : HlawkaSchatten.DiagonalCutoff16.cyclicConstant_upper16
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T21:36:59.016665+00:00
-- url     : https://prove2.me/theorems/5ac0c9e2-2d15-43f4-9d57-1e3a8e50d5d5
-- title:
--   The cyclic Hlawka constant is at most p/2 for 16 <= p <= 32
-- statement:
--   Let $K_p$ be the cyclic Hlawka constant defined by
--   $$A_p(t)=(t^p+2)^{1/p},\qquad B_p(t)=(2|1-t|^p+2^p)^{1/p},$$
--   $$K_p=\sup_{1/2\le t\le2}\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)}.$$
--   For every real exponent $p$ with $16\le p\le32$,
--   $$K_p\le\frac p2.$$
--   This extends the scalar upper-bound component used in the accepted cutoff-21 proof to the range needed for cutoff 16. It concerns the explicitly defined cyclic constant, and makes no assertion that the sharp Hlawka bound for arbitrary triples has already been proved.
-- source:
--   Cutoff-16 extension of Yuxuan Xu's accepted Prove2Me scalar proof, submission e696f6e8-38ad-49b3-b319-6be8f8688015; original cutoff-21 theorem 6a6590b3-eb58-4251-9cc2-59e3721f34f5. See https://prove2.me/theorems/6a6590b3-eb58-4251-9cc2-59e3721f34f5 . The changed lower cutoff and strengthened root estimates are proved afresh in the submitted source.

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff16.cyclicConstant_upper16 {p : ℝ} (hp : 16 ≤ p) (hp32 : p ≤ 32) :
    cyclicConstant p ≤ p/2 := by sorry
