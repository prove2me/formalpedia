-- Prove2me | Theorems.Thm_OAI_SingleFold_PointCompiler_PointSF_smul
-- name    : OAI.SingleFold.PointCompiler.PointSF.smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:55:18.091013+00:00
-- url     : https://prove2.me/theorems/addd5f40-10c8-4423-ba7c-0a3e19c755df
-- title:
--   Point-SF maps are closed under fixed scalar multiples
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. Let $E$ be the curve $y^2=x^3-25x$ over $\mathbb{Q}$. A point code consists of a flag and two rational codes $(p,n,d,t,s,q)$ with value $(p-n)/d$, i.e. $13$ natural numbers; it is valid if the rational codes are valid and either the flag is $1$ and $x=y=0$ (the point $O$) or the flag is $0$ and $y^2=x^3-25x$. Every point $P$ has a canonical code $\mathrm{code}(P)$. A map $f:\mathbb{N}^\alpha\to E(\mathbb{Q})$ is point-SF if the graph of $x\mapsto\mathrm{code}(f(x))\in\mathbb{N}^{13}$ is SF. If $f$ is point-SF and $n\in\mathbb{N}$, then so is
--   $$
--   x\mapsto n\,f(x) .
--   $$
--
--   Each fixed multiple costs only a bounded number of additional witnesses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/FunctionalCompiler.lean#L126-L141

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler

open OAI OAI.SingleFold OAI.SingleFold.PointCompiler
open Compiler RationalCompiler
variable {α β : Type} {f g : (α → ℕ) → E.Point}

theorem OAI.SingleFold.PointCompiler.PointSF.smul (n : ℕ) (hf : PointSF f) : PointSF (fun z => n • f z) := by sorry
