-- Prove2me | Theorems.Thm_IntMul_GaussianNormalization_normalized_fourth_root
-- name    : IntMul.GaussianNormalization.normalized_fourth_root
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T17:22:48.06326+00:00
-- url     : https://prove2.me/theorems/0d22bb90-7b1b-498b-a61b-7d62b27d0e5d
-- title:
--   Exact fourth-root normalization of a Gaussian integer of norm 2^r
-- statement:
--   Let $z$ be a Gaussian integer with Gaussian norm $N(z)=2^r$, where $r$ is a nonnegative integer. Then
--   $$\left(z\left(\frac{1-i}{2}\right)^r\right)^4=1.$$
--   Thus the normalized value is an exact fourth root of unity. This supplies the scalar normalization step in the complex binary residual transform used by the integer-multiplication κ construction. In that application a separate character-orthogonality argument establishes the required norm of the quadratic Gauss sum. The present theorem is the unconditional Gaussian-integer arithmetic step; it does not assert the correctness or time bound of a multiplication machine.
-- source:
--   CrocSwap/integer-mult-bounds, commit 3b6b66891c0ac888521cf591fe306c6286601d4f, notes/endpoint-gauge-complex.tex, subsection “A normal form for every nondegenerate binary residual”, assertion that S_q b^r is a fourth root of unity. https://github.com/CrocSwap/integer-mult-bounds/blob/3b6b66891c0ac888521cf591fe306c6286601d4f/notes/endpoint-gauge-complex.tex . This is an alternative arithmetic proof of the scalar step using divisibility by 1+i, rather than quadratic-form block classification.

import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic

theorem IntMul.GaussianNormalization.normalized_fourth_root
    (r : ℕ) (z : GaussianInt) (hz : z.norm = (2 : ℤ) ^ r) :
    ((z : ℂ) * ((1 - Complex.I) / 2) ^ r) ^ 4 = 1 := by sorry
