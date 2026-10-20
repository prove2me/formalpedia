-- Prove2me | Theorems.Thm_OAI_SingleFold_RationalCompiler_valid_semi
-- name    : OAI.SingleFold.RationalCompiler.valid_semi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:49:29.932623+00:00
-- url     : https://prove2.me/theorems/a6550ac0-2979-46c3-be92-82dfe39e08f6
-- title:
--   Validity of finitely many rational codes is semi-representable
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. For a finite set $\alpha$ and $z\in\mathbb{N}^{\alpha\times\{0,\dots,5\}}$, let $\mathrm{Valid}(z)$ say that each block $(p_i,n_i,d_i,t_i,s_i,q_i)$ is a valid rational code:
--   $$
--   p_in_i=0,\qquad d_i=1+t_i+s_i,\qquad(p_i+n_i)t_i+d_i=1+q_id_i .
--   $$
--   Then $\mathrm{Valid}$ is semi-representable.
--
--   Both validity and invalidity of codes can therefore be used inside single-fold constructions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/RationalCodes.lean#L343-L357

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes

open OAI OAI.SingleFold OAI.SingleFold.RationalCompiler
open Compiler

theorem OAI.SingleFold.RationalCompiler.valid_semi {α : Type} [Finite α] : Semi (@Valid α) := by sorry
