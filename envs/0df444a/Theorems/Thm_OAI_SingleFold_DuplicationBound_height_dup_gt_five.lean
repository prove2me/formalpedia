-- Prove2me | Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_gt_five
-- name    : OAI.SingleFold.DuplicationBound.height_dup_gt_five
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:06:11.34451+00:00
-- url     : https://prove2.me/theorems/43a35999-dbb6-4d82-a03b-282a17aa1f57
-- title:
--   Doubles of non-2-torsion points have height above 5
-- statement:
--   For a rational $x$ let $h(x)=\max(|\mathrm{num}(x)|,\mathrm{den}(x))$ in lowest terms, and let $\mathrm{dup}(x)=\dfrac{(x^2+25)^2}{4x(x^2-25)}$ be the $x$-coordinate of $2P$ on $y^2=x^3-25x$ when $x(P)=x$. If $y^2=x^3-25x$ with $y\ne0$, then
--   $$
--   h(\mathrm{dup}(x))>5 .
--   $$
--
--   So the $x$-coordinate of any double $2P\ne O$ has height above $5$, which separates such points from the $2$-torsion points $(0,0)$ and $(\pm5,0)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Duplication.lean#L190-L202

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication

open OAI OAI.SingleFold OAI.SingleFold.DuplicationBound

theorem OAI.SingleFold.DuplicationBound.height_dup_gt_five {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    5 < height (dupX x) := by sorry
