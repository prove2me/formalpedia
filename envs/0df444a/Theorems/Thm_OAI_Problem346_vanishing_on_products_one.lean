-- Prove2me | Theorems.Thm_OAI_Problem346_vanishing_on_products_one
-- name    : OAI.Problem346.vanishing_on_products_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:27:35.385263+00:00
-- url     : https://prove2.me/theorems/f832d72a-5294-4b37-bad3-9164528da1a0
-- title:
--   One-argument case of diagonal vanishing: a form on $\operatorname{Sym}^bV$ vanishing on all monomials is zero
-- statement:
--   Let $V$ be a complex vector space and let $b\in\mathbb{N}$. Write $\operatorname{Sym}(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\operatorname{Sym}^nV\subseteq\operatorname{Sym}(V)$ be the complex linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$. For $n=0$ this is the span of the empty product $1$. For $(v_0,\dots,v_{n-1})\in V^n$ write $[v_0,\dots,v_{n-1}]=v_0\cdots v_{n-1}\in\operatorname{Sym}^nV$ and call it a monomial.
--
--   **Theorem.** Let $T\colon\operatorname{Sym}^bV\to\mathbb{C}$ be a multilinear form in a single argument, that is, a $\mathbb{C}$-linear functional on $\operatorname{Sym}^bV$. If
--
--   $$
--   T\bigl([u_0,\dots,u_{b-1}]\bigr)=0\qquad\text{for all }u_0,\dots,u_{b-1}\in V,
--   $$
--
--   then $T=0$.
--
--   This is the case $a=1$ of the diagonal vanishing theorem for symmetric $a$-linear forms on $\operatorname{Sym}^bV$. With a single argument, the diagonal value $T(P)$ at a monomial $P$ is just the value at $P$, so no symmetry hypothesis and no relation between $a$ and $b$ are needed. It is the base case of the induction on the number of arguments.
--
--   **Formalization Note** $\operatorname{Sym}^nV$ is `SymPow n V`, the subtype of the submodule `symPowSubmodule n V` of Mathlib's `SymmetricAlgebra ℂ V`, and $[v_0,\dots,v_{n-1}]$ is `symMonomial n V v`. The form $T$ has type `SymmetricMultilinearForm 1 b V`, i.e. it is a multilinear map on `Fin 1 → SymPow b V`, and the hypothesis is stated with the constant one-entry tuple `fun _ => symMonomial b V u`. No symmetry predicate is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/VanishingOne.lean#L9-L23

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap

open OAI OAI.Problem346
universe u

theorem OAI.Problem346.vanishing_on_products_one (V : Type u) [AddCommGroup V] [Module ℂ V]
    (b : ℕ) (T : SymmetricMultilinearForm 1 b V)
    (h : ∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) : T = 0 := by sorry
