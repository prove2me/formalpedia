-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_mulRel_sf
-- name    : OAI.SingleFold.PointCompiler.mulRel_sf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:53:56.624617+00:00
-- url     : https://prove2.me/theorems/bf52dac8-a4ca-4c55-8513-541844ad334a
-- title:
--   Scalar multiplication by a fixed integer is single-fold
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. Let $E$ be the curve $y^2=x^3-25x$ over $\mathbb{Q}$. A point code consists of a flag and two rational codes $(p,n,d,t,s,q)$ with value $(p-n)/d$, i.e. $13$ natural numbers; it is valid if the rational codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$) or the flag is $0$ and $y^2=x^3-25x$. Every point $P$ has a canonical code $\mathrm{code}(P)$. For every $n\in\mathbb{N}$ and all placements $f,g$ of two code slots, the relation
--   $$
--   \exists P\in E(\mathbb{Q}):\ z\circ f=\mathrm{code}(P)\ \wedge\ z\circ g=\mathrm{code}(nP)
--   $$
--   is SF.
--
--   The multiple $nP$ is computed by $n$ additions, each step adding one uniquely determined intermediate code.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean#L367-L397

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point
variable {α : Type}

theorem OAI.SingleFold.PointCompiler.mulRel_sf (n : ℕ) : ∀ {α : Type} (f g : Var → α),
    SF (fun z => MulRel n (fromTuple (z ∘ f)) (fromTuple (z ∘ g))) := by sorry
