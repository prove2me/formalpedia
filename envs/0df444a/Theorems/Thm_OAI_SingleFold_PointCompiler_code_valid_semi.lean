-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_code_valid_semi
-- name    : OAI.SingleFold.PointCompiler.code_valid_semi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:50:45.521987+00:00
-- url     : https://prove2.me/theorems/07ad128a-f74d-46c4-abaa-b10b2e4f9d0a
-- title:
--   Validity of a point code is semi-representable
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. Let $E$ be the curve $y^2=x^3-25x$ over $\mathbb{Q}$. A point code consists of a flag and two rational codes $(p,n,d,t,s,q)$ with value $(p-n)/d$, i.e. $13$ natural numbers; it is valid if the rational codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$) or the flag is $0$ and $y^2=x^3-25x$. Every point $P$ has a canonical code $\mathrm{code}(P)$. Then the relation on $z\in\mathbb{N}^{13}$
--   $$
--   z\text{ is a valid point code}
--   $$
--   is semi-representable.
--
--   This is the basic membership test for points of $E$ in the compiler.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean#L69-L94

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

theorem OAI.SingleFold.PointCompiler.code_valid_semi : Semi (fun z => (fromTuple z).Valid) := by sorry
