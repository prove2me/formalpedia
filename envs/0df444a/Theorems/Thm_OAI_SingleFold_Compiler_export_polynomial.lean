-- Prove2me | Theorems.Thm_OAI_SingleFold_Compiler_export_polynomial
-- name    : OAI.SingleFold.Compiler.export_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T16:48:59.07642+00:00
-- url     : https://prove2.me/theorems/13df57dd-a040-47e5-b73c-5b99cbda6b93
-- title:
--   A single-fold representation as an explicit integer polynomial
-- statement:
--   A relation $R$ on $\mathbb{N}^\alpha$ is SF (single-fold Diophantine) if there are a finite set $V$ and an integer polynomial $P$ in $\alpha\sqcup V$ with $R(x)\iff\exists w\in\mathbb{N}^V\,P(x,w)=0$, where for each $x$ at most one $w$ solves $P(x,w)=0$. It is semi-representable if both $R$ and $\neg R$ are SF. If $R$ has a single-fold representation, then there are $m\ge1$ and $p\in\mathbb{Z}[x_\alpha,w_1,\dots,w_m]$ with
--   $$
--   R(x)\iff\exists\,w\in\mathbb{N}^m\ p(x,w)=0,
--   $$
--   and for every $x$, any two $w,w'\in\mathbb{N}^m$ with $p(x,w)=p(x,w')=0$ are equal.
--
--   This converts the compiler's internal polynomial into a standard multivariate polynomial with a positive number of witness variables.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/PolynomialCompiler.lean#L254-L300

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler

open OAI OAI.SingleFold OAI.SingleFold.Compiler

theorem OAI.SingleFold.Compiler.export_polynomial {α : Type} {R : (α → ℕ) → Prop} (r : Representation R) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ p : MvPolynomial (α ⊕ Fin m) ℤ,
      (∀ x, R x ↔ ∃ w : Fin m → ℕ, p.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w j:ℤ)))=0) ∧
      (∀ (x : α → ℕ) (w w' : Fin m → ℕ), p.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w j:ℤ)))=0 →
        p.eval (Sum.elim (fun i => (x i:ℤ)) (fun j => (w' j:ℤ)))=0 → w=w') := by sorry
