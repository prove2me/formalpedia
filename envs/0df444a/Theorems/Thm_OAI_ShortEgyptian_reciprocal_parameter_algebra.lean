-- Prove2me | Theorems.Thm_OAI_ShortEgyptian_reciprocal_parameter_algebra
-- name    : OAI.ShortEgyptian.reciprocal_parameter_algebra
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:27:14.107744+00:00
-- url     : https://prove2.me/theorems/64d87ec5-a205-4482-ac2b-e25b0c638864
-- title:
--   Parameter inequalities for the exponential-sum estimate of reciprocal phases
-- statement:
--   Let $r\in\mathbb{N}$ and let $A,F,U,v,b,L$ be real numbers with
--   $$
--   A\ge1,\quad F\ge1,\quad v\ge1,\quad U>0,\quad b\ge0,\quad 0\le L\le2v,
--   $$
--   and assume
--   $$
--   (18A)^4F^2\,2^{2r}\,v^{2r+4}\le U,\qquad1\le U^3b^2,\qquad Ub^2\le1 .
--   $$
--   Then:
--
--   1. $18v\le U$;
--   2. $(18v/U)^2\le Fb/A$;
--   3. $L^r\,(Fb/A)\le\bigl(1/(18Av)\bigr)^2$.
--
--   This is a purely algebraic step. It says that if $U^{-3/2}\le b\le U^{-1/2}$ and $U$ is large compared with a fixed power of $v$, then $Fb/A$ lies in the window required by the exponential-sum estimate for $e(Z/n)$: it is large compared with $(v/U)^2$, and small even after multiplication by $L^r$. In the application $A=3^{r+3}$, $F=(r+2)!$, $v=T^{2^r}$, $L=\lceil v\rceil$ and $b=Z/U^{r+3}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/ShortEgyptian/ParameterBounds.lean#L10-L81

import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds

open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset

theorem OAI.ShortEgyptian.reciprocal_parameter_algebra (r : ℕ) (A F U v b L : ℝ)
    (hA : 1 ≤ A) (hF : 1 ≤ F) (hv : 1 ≤ v) (hU : 0 < U)
    (hb : 0 ≤ b) (hL : 0 ≤ L) (hLv : L ≤ 2 * v)
    (hlarge : (18 * A) ^ 4 * F ^ 2 * (2 : ℝ) ^ (2 * r) * v ^ (2 * r + 4) ≤ U)
    (hbaseLow : 1 ≤ U ^ 3 * b ^ 2) (hbaseHigh : U * b ^ 2 ≤ 1) :
    18 * v ≤ U ∧ (18 * v / U) ^ 2 ≤ F * b / A ∧
      L ^ r * (F * b / A) ≤ (1 / (18 * A * v)) ^ 2 := by sorry
