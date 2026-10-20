-- Prove2me | Theorems.Thm_OAI_SingleFold_DuplicationBound_small_points
-- name    : OAI.SingleFold.DuplicationBound.small_points
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T17:03:31.795155+00:00
-- url     : https://prove2.me/theorems/5dab9991-5fab-4b0e-a36c-500424a5167b
-- title:
--   Rational points of $y^2=x^3-25x$ with $x$ of small height
-- statement:
--   For a rational $x$ let $h(x)=\max(|\mathrm{num}(x)|,\mathrm{den}(x))$ in lowest terms, and let $\mathrm{dup}(x)=\dfrac{(x^2+25)^2}{4x(x^2-25)}$ be the $x$-coordinate of $2P$ on $y^2=x^3-25x$ when $x(P)=x$. If $y^2=x^3-25x$ with $x,y\in\mathbb{Q}$ and $h(x)<185$, then
--   $$
--   x\in\Bigl\{0,\ 5,\ -5,\ -4,\ 45,\ \tfrac{25}{4},\ -\tfrac59\Bigr\} .
--   $$
--
--   This finite list covers the base cases of the height-growth argument. It is obtained by a finite search.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Duplication.lean#L130-L164

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

theorem OAI.SingleFold.DuplicationBound.small_points {x y : ℚ} (he : y^2=x^3-25*x) (hH : height x < 185) :
    x=0 ∨ x=5 ∨ x= -5 ∨ x= -4 ∨ x=45 ∨ x=25/4 ∨ x= -5/9 := by sorry
