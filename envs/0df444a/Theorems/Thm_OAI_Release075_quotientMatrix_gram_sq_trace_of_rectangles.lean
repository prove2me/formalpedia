-- Prove2me | Theorems.Thm_OAI_Release075_quotientMatrix_gram_sq_trace_of_rectangles
-- name    : OAI.Release075.quotientMatrix_gram_sq_trace_of_rectangles
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T07:32:43.902087+00:00
-- url     : https://prove2.me/theorems/c962e4e1-202a-424c-bab7-332f013d0b21
-- title:
--   Fourth-moment trace of a rectangle-preserving quotient matrix
-- statement:
--   For a finite group $F$, write $\rho(x)$ for the $F\times F$ permutation matrix of left multiplication, $\rho(x)_{a,b}=[a=xb]$. For $g:\iota\times\iota\to F$ the quotient matrix $Y(g)$ is the $(\iota\times F)\times(\iota\times F)$ block matrix with blocks $\rho(g(u,v))$. The family $g$ has surviving rectangles if $g(u,v)g(u',v)^{-1}g(u',v')g(u,v')^{-1}\ne1$ whenever $u\ne u'$ and $v\ne v'$. If $g$ has surviving rectangles and $r=|\iota|$, then over any commutative ring
--   $$
--   \operatorname{tr}\bigl((YY^{\top})^2\bigr)=(2r^3-r^2)\,|F| .
--   $$
--
--   Only the degenerate index choices with $u=u'$ or $v=v'$ contribute.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/MatrixRank.lean#L368-L393

import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank

open OAI OAI.Release075
universe u v
open scoped BigOperators

theorem OAI.Release075.quotientMatrix_gram_sq_trace_of_rectangles {ι F R : Type*} [Fintype ι]
    [Group F] [Fintype F] [DecidableEq F] [CommRing R]
    (g : ι → ι → F) (hg : RectanglesSurvive g) :
    ((quotientMatrix (R := R) g * (quotientMatrix g).transpose) *
      (quotientMatrix g * (quotientMatrix g).transpose)).trace =
      (2 * (Fintype.card ι : R) ^ 3 - (Fintype.card ι : R) ^ 2) * Fintype.card F := by sorry
