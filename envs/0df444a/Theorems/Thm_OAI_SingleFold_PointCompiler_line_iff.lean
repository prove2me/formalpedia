-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_line_iff
-- name    : OAI.SingleFold.PointCompiler.line_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:52:18.409071+00:00
-- url     : https://prove2.me/theorems/d727fea7-471a-4dac-ab04-b535ceb6687f
-- title:
--   The chord-tangent relation in solved form
-- statement:
--   For rationals with $d\ne0$, the relation
--   $$
--   d^2(x_3+x_1+x_2)=n^2,\qquad d(y_3+y_1)=n(x_1-x_3)
--   $$
--   holds if and only if $x_3=\lambda^2-x_1-x_2$ and $y_3=\lambda(x_1-x_3)-y_1$, where $\lambda=n/d$.
--
--   These are the addition formulas of a Weierstrass curve $y^2=x^3+ax+b$ with slope $\lambda$. Writing them with numerator and denominator avoids division in the polynomial encoding.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean#L98-L111

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem OAI.SingleFold.PointCompiler.line_iff {d n x₁ x₂ y₁ x₃ y₃ : ℚ} (hd : d≠0) :
    Line d n x₁ x₂ y₁ x₃ y₃ ↔
      x₃=(n/d)^2-x₁-x₂ ∧ y₃=n/d*(x₁-x₃)-y₁ := by sorry
