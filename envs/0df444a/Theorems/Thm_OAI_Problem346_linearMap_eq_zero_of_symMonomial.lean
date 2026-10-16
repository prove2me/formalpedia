-- Prove2me | Theorems.Thm_OAI_Problem346_linearMap_eq_zero_of_symMonomial
-- name    : OAI.Problem346.linearMap_eq_zero_of_symMonomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:15:52.192187+00:00
-- url     : https://prove2.me/theorems/4c6530bc-7390-428e-a330-d38e0716ecbb
-- title:
--   A linear map on the $n$-th symmetric power that vanishes on all products of $n$ vectors is zero
-- statement:
--   Let $V$ and $W$ be complex vector spaces and let $n\in\mathbb{N}$. Write $\operatorname{Sym}(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\operatorname{Sym}^nV\subseteq\operatorname{Sym}(V)$ be the complex linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$. For $n=0$ this is the span of the empty product $1$. For $(v_0,\dots,v_{n-1})\in V^n$ write $[v_0,\dots,v_{n-1}]=v_0\cdots v_{n-1}\in\operatorname{Sym}^nV$ and call it a monomial.
--
--   **Theorem.** Let $\varphi\colon\operatorname{Sym}^nV\to W$ be a $\mathbb{C}$-linear map such that
--
--   $$
--   \varphi\bigl([v_0,\dots,v_{n-1}]\bigr)=0\qquad\text{for all }(v_0,\dots,v_{n-1})\in V^n .
--   $$
--
--   Then $\varphi=0$.
--
--   This is the basic extensionality principle for linear maps out of a symmetric power. To show that such a map vanishes, or that two such maps agree (apply the theorem to their difference), it is enough to test on products of vectors. It is used, for example, to show that a linear functional on $\operatorname{Sym}^a(\operatorname{Sym}^bV)$ is zero once the multilinear form it induces on $\operatorname{Sym}^bV$ is zero.
--
--   **Formalization Note** $\operatorname{Sym}^nV$ is `SymPow n V`, the subtype of the submodule `symPowSubmodule n V` of Mathlib's `SymmetricAlgebra ℂ V`, and $[v_0,\dots,v_{n-1}]$ is `symMonomial n V v`. No finiteness assumption is made on $V$ or $W$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/MonomialMultilinear.lean#L51-L69

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

open OAI OAI.Problem346
open scoped BigOperators
universe u v

theorem OAI.Problem346.linearMap_eq_zero_of_symMonomial (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] {W : Type v} [AddCommGroup W] [Module ℂ W]
    (φ : SymPow n V →ₗ[ℂ] W)
    (hφ : ∀ x : Fin n → V, φ (symMonomial n V x) = 0) : φ = 0 := by sorry
