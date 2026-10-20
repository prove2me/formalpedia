-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_addEq_encode
-- name    : OAI.SingleFold.PointCompiler.addEq_encode
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:52:51.83306+00:00
-- url     : https://prove2.me/theorems/a44f7f4c-dfdd-4f9b-9a43-b45b622d1c05
-- title:
--   The addition relation on codes is exactly the group law
-- statement:
--   Let $E$ be the curve $y^2=x^3-25x$ over $\mathbb{Q}$. A point code consists of a flag and two rational codes $(p,n,d,t,s,q)$ with value $(p-n)/d$, i.e. $13$ natural numbers; it is valid if the rational codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$) or the flag is $0$ and $y^2=x^3-25x$. Every point $P$ has a canonical code $\mathrm{code}(P)$. Let $\mathrm{AddEq}(a,b,c)$ be the case-split addition relation on point codes: $c=b$ if $a=O$; $c=a$ if $b=O$; $c=O$ if $x_a=x_b$ and $y_a+y_b=0$; the chord through the two points if $x_a\ne x_b$; and the tangent of slope $(3x_a^2-25)/(2y_a)$ otherwise. Then for all points $P,Q,R$,
--   $$
--   \mathrm{AddEq}(\mathrm{code}(P),\mathrm{code}(Q),\mathrm{code}(R))\iff P+Q=R .
--   $$
--
--   The group law of $E$ is captured by polynomial relations among the code values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean#L153-L192

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem OAI.SingleFold.PointCompiler.addEq_encode (P Q R : E.Point) : AddEq (encode P) (encode Q) (encode R) ↔ P+Q=R := by sorry
