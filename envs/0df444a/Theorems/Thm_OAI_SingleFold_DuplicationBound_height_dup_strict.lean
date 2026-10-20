-- Prove2me | Theorems.Thm_OAI_SingleFold_DuplicationBound_height_dup_strict
-- name    : OAI.SingleFold.DuplicationBound.height_dup_strict
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:05:28.086297+00:00
-- url     : https://prove2.me/theorems/7adc897a-7467-4fe6-8028-559d5f6aed07
-- title:
--   Doubling a non-2-torsion point strictly increases the height of $x$
-- statement:
--   For a rational $x$ let $h(x)=\max(|\mathrm{num}(x)|,\mathrm{den}(x))$ in lowest terms, and let $\mathrm{dup}(x)=\dfrac{(x^2+25)^2}{4x(x^2-25)}$ be the $x$-coordinate of $2P$ on $y^2=x^3-25x$ when $x(P)=x$. If $y^2=x^3-25x$ with $y\ne0$, then
--   $$
--   h(x)<h(\mathrm{dup}(x)) .
--   $$
--
--   Consequently the heights of $P,2P,4P,\dots$ strictly increase for every point $P$ that is not $2$-torsion. In particular such points have infinite order.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Duplication.lean#L166-L188

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

theorem OAI.SingleFold.DuplicationBound.height_dup_strict {x y : ℚ} (he : y^2=x^3-25*x) (hy : y ≠ 0) :
    height x < height (dupX x) := by sorry
