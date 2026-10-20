-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_add_general_sf
-- name    : OAI.SingleFold.PointCompiler.add_general_sf
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:53:22.441365+00:00
-- url     : https://prove2.me/theorems/b50067ae-3706-4069-a4fc-63fbc069954c
-- title:
--   Point addition on three code slots is single-fold
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. Let $E$ be the curve $y^2=x^3-25x$ over $\mathbb{Q}$. A point code consists of a flag and two rational codes $(p,n,d,t,s,q)$ with value $(p-n)/d$, i.e. $13$ natural numbers; it is valid if the rational codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$) or the flag is $0$ and $y^2=x^3-25x$. Every point $P$ has a canonical code $\mathrm{code}(P)$. For any three placements $f,g,h:\{1,\dots,13\}\to\alpha$ of code coordinates among the variables, the relation on $z\in\mathbb{N}^\alpha$
--   $$
--   z\circ f,\ z\circ g,\ z\circ h\ \text{are valid codes and}\ \mathrm{AddEq}(z\circ f,z\circ g,z\circ h)
--   $$
--   is SF.
--
--   The slots may overlap, so the same lemma covers doubling and other coincident configurations.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/EllipticCoordinates.lean#L349-L365

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
open WeierstrassCurve.Affine.Point
variable {α : Type}

theorem OAI.SingleFold.PointCompiler.add_general_sf (f g h : Var → α) : SF (fun z =>
    (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧ (fromTuple (z ∘ h)).Valid ∧
    AddEq (fromTuple (z ∘ f)) (fromTuple (z ∘ g)) (fromTuple (z ∘ h))) := by sorry
