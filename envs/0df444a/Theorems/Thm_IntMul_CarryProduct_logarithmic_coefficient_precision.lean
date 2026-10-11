-- Prove2me | Theorems.Thm_IntMul_CarryProduct_logarithmic_coefficient_precision
-- name    : IntMul.CarryProduct.logarithmic_coefficient_precision
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T15:31:38.103742+00:00
-- url     : https://prove2.me/theorems/a251cb36-6c24-4d55-8184-7d4d30ab946c
-- title:
--   Uniform three-block-bit precision for every convolution coefficient and carry
-- statement:
--   Let $x,y$ be binary operand words, $W=|x|+|y|$ and $B\ge\lg W$, where $\lg W=\max(\lceil\log_2 W\rceil,1)$. Split the words into base-$2^B$ digits and let $(a_j)$ be their full padded convolution coefficient array. Its minimal sufficient coefficient precision is
--
--   $$N_0=2B+\left\lceil\log_2\min(m_x,m_y)\right\rceil,$$
--
--   where $m_x,m_y$ are the respective block counts. Then
--
--   $$N_0\le3B,$$
--
--   and every coefficient-plus-carry sum in the low-to-high normalization pass satisfies
--
--   $$a+c_j<2^{3B}$$
--
--   for every coefficient $a$ of the array and every carry position $j$. This gives a uniform sufficient $3B$-bit precision using only a logarithmic block-size parameter, removing the need to compute an exact block-count-dependent coefficient precision. Empty and leading-zero operand words are included.
-- source:
--   Original logarithmic coefficient/carry precision bound. Uses exact accepted convolution and carry bounds, with owned block-count and power inequalities. Written by Codex.

import Definitions.Def_IntMul_CarryProduct
import Mathlib.Tactic

open IntMul IntMul.CarryProduct

theorem IntMul.CarryProduct.logarithmic_coefficient_precision (B : ℕ) (x y : List Bool)
    (hb : lg (x.length+y.length)≤B) :
    coefficientWidth B x y≤3*B ∧
      ∀ a ∈ CarryNormalization.coefficients B x y, ∀ j : ℕ,
        a+CarryNormalization.carryAt (2^B) (CarryNormalization.coefficients B x y) 0 j<2^(3*B) := by sorry
