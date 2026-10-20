-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_PointSF_height
-- name    : OAI.SingleFold.PointCompiler.PointSF.height
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:57:07.167894+00:00
-- url     : https://prove2.me/theorems/a09fd0ca-d605-4b7d-9c46-44706f999fc7
-- title:
--   Heights of fixed multiples of point-SF maps are single-fold
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. Let $E$ be the curve $y^2=x^3-25x$ over $\mathbb{Q}$. A point code consists of a flag and two rational codes $(p,n,d,t,s,q)$ with value $(p-n)/d$, i.e. $13$ natural numbers; it is valid if the rational codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$) or the flag is $0$ and $y^2=x^3-25x$. Every point $P$ has a canonical code $\mathrm{code}(P)$. A map $f:\mathbb{N}^\alpha\to E(\mathbb{Q})$ is point-SF if the graph of $x\mapsto\mathrm{code}(f(x))\in\mathbb{N}^{13}$ is SF. The height of a code is $\max(|\mathrm{num}(x)|,\mathrm{den}(x))$ of its $x$-value. If $f$ is point-SF and $m\in\mathbb{N}$, then the graph of
--   $$
--   x\mapsto\mathrm{height}\bigl(\mathrm{code}(m\,f(x))\bigr)\in\mathbb{N}
--   $$
--   is SF.
--
--   Heights of multiples are the numerical quantities from which the growth function is built.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean#L142-L156

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
variable {α β : Type} {f g : (α → ℕ) → E.Point}

theorem OAI.SingleFold.PointCompiler.PointSF.height (m : ℕ) (hf : PointSF f) :
    MapSF (fun z (_ : Unit) => (encode (m • f z)).height) := by sorry
