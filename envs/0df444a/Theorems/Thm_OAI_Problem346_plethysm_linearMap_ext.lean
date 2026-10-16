-- Prove2me | Theorems.Thm_OAI_Problem346_plethysm_linearMap_ext
-- name    : OAI.Problem346.plethysm_linearMap_ext
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:19:37.814732+00:00
-- url     : https://prove2.me/theorems/7849f0c0-ec64-47a1-b8d1-e6816cf4cfba
-- title:
--   Linear maps on $\operatorname{Sym}^b(\operatorname{Sym}^aV)$ are determined by their values on monomials of monomials
-- statement:
--   Let $V$ and $W$ be complex vector spaces and let $a,b\in\mathbb{N}$. Write $\operatorname{Sym}(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\operatorname{Sym}^nV\subseteq\operatorname{Sym}(V)$ be the complex linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$. For $n=0$ this is the span of the empty product $1$. For $(v_0,\dots,v_{n-1})\in V^n$ write $[v_0,\dots,v_{n-1}]=v_0\cdots v_{n-1}\in\operatorname{Sym}^nV$ and call it a monomial. Applying the same construction to the complex vector space $\operatorname{Sym}^aV$ gives $\operatorname{Sym}^b(\operatorname{Sym}^aV)$. For an array $x=(x_{j,i})$ of vectors of $V$, with $0\le j<b$ and $0\le i<a$, the corresponding double monomial is
--
--   $$
--   M(x)=\Bigl[\,[x_{0,0},\dots,x_{0,a-1}],\ \dots,\ [x_{b-1,0},\dots,x_{b-1,a-1}]\,\Bigr]\in\operatorname{Sym}^b(\operatorname{Sym}^aV).
--   $$
--
--   **Theorem.** Let $f,g\colon\operatorname{Sym}^b(\operatorname{Sym}^aV)\to W$ be $\mathbb{C}$-linear maps with $f(M(x))=g(M(x))$ for every such array $x$. Then $f=g$.
--
--   The space $\operatorname{Sym}^b(\operatorname{Sym}^aV)$ is spanned by products of $b$ arbitrary elements of $\operatorname{Sym}^aV$. The theorem says that it suffices to test linear maps on the smaller family of products of $b$ monomials. This is how a linear map out of the plethysm is pinned down by a formula on double monomials. In particular, a linear map $\operatorname{Sym}^b(\operatorname{Sym}^aV)\to\operatorname{Sym}^a(\operatorname{Sym}^bV)$ is uniquely determined by such a formula, which is the uniqueness part of the Foulkes map.
--
--   **Formalization Note** $\operatorname{Sym}^nV$ is `SymPow n V`, the subtype of the submodule `symPowSubmodule n V` of Mathlib's `SymmetricAlgebra ℂ V`, and $[v_0,\dots,v_{n-1}]$ is `symMonomial n V v`. The array $x$ is a function `Fin b → Fin a → V`, and $M(x)$ is `symMonomial b (SymPow a V) (fun j => symMonomial a V (x j))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Spanning.lean#L64-L83

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

open OAI OAI.Problem346
open scoped BigOperators
universe u v

theorem OAI.Problem346.plethysm_linearMap_ext (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    {W : Type v} [AddCommGroup W] [Module ℂ W]
    (f g : SymPow b (SymPow a V) →ₗ[ℂ] W)
    (h : ∀ x : Fin b → Fin a → V,
      f (symMonomial b (SymPow a V) (fun j => symMonomial a V (x j))) =
      g (symMonomial b (SymPow a V) (fun j => symMonomial a V (x j)))) : f = g := by sorry
