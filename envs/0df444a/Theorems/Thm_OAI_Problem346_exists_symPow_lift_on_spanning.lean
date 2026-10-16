-- Prove2me | Theorems.Thm_OAI_Problem346_exists_symPow_lift_on_spanning
-- name    : OAI.Problem346.exists_symPow_lift_on_spanning
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:24:07.047156+00:00
-- url     : https://prove2.me/theorems/0b7aa63b-2d4a-43f9-9e69-8e71df49c503
-- title:
--   Symmetric, separately linear formulas on spanning generators induce linear maps on $\operatorname{Sym}^nV$
-- statement:
--   Let $V$ and $W$ be complex vector spaces and let $n\in\mathbb{N}$. Write $\operatorname{Sym}(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\operatorname{Sym}^nV\subseteq\operatorname{Sym}(V)$ be the complex linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$. For $n=0$ this is the span of the empty product $1$. For $(v_0,\dots,v_{n-1})\in V^n$ write $[v_0,\dots,v_{n-1}]=v_0\cdots v_{n-1}\in\operatorname{Sym}^nV$ and call it a monomial. Let $X$ be a set and $s\colon X\to V$ a map whose image spans $V$. For $x=(x_0,\dots,x_{n-1})\in X^n$, a slot $i\in\{0,\dots,n-1\}$ and $y\in X$, let $x[i\leftarrow y]$ denote $x$ with its $i$-th entry replaced by $y$. Let $F\colon X^n\to W$ be a function such that:
--
--   1. (separate linearity) for every $x\in X^n$ and every slot $i$ there is a $\mathbb{C}$-linear map $L\colon V\to W$ with $L(s(y))=F(x[i\leftarrow y])$ for all $y\in X$;
--   2. (symmetry) $F(x_{\sigma(0)},\dots,x_{\sigma(n-1)})=F(x_0,\dots,x_{n-1})$ for every permutation $\sigma$ of $\{0,\dots,n-1\}$ and every $x\in X^n$.
--
--   **Theorem.** There is a $\mathbb{C}$-linear map $L\colon\operatorname{Sym}^nV\to W$ such that
--
--   $$
--   L\bigl([s(x_0),\dots,s(x_{n-1})]\bigr)=F(x_0,\dots,x_{n-1})\qquad\text{for all }(x_0,\dots,x_{n-1})\in X^n .
--   $$
--
--   This is a construction principle for linear maps out of a symmetric power. It suffices to give a formula on products of spanning generators, symmetric in the factors and linear in each factor separately. In the construction of the Foulkes map it is applied with $X=V^a$ and $s$ the monomial map $V^a\to\operatorname{Sym}^aV$, so that the defining formula on products of monomials yields a linear map on $\operatorname{Sym}^b(\operatorname{Sym}^aV)$.
--
--   **Formalization Note** $\operatorname{Sym}^nV$ is `SymPow n V`, the subtype of the submodule `symPowSubmodule n V` of Mathlib's `SymmetricAlgebra ℂ V`, and $[v_0,\dots,v_{n-1}]$ is `symMonomial n V v`. The set $X$ is an arbitrary type, the spanning hypothesis is `Submodule.span ℂ (Set.range s) = ⊤`, and $x[i\leftarrow y]$ is `Function.update x i y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/GeneratorLift.lean#L10-L40

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

open OAI OAI.Problem346

theorem OAI.Problem346.exists_symPow_lift_on_spanning
    {n : ℕ} {X V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (s : X → V) (hs : Submodule.span ℂ (Set.range s) = ⊤)
    (F : (Fin n → X) → W)
    (hlinear : ∀ x : Fin n → X, ∀ i : Fin n,
      ∃ L : V →ₗ[ℂ] W, ∀ y, L (s y) = F (Function.update x i y))
    (hsym : ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → X),
      F (fun i => x (σ i)) = F x) :
    ∃ L : SymPow n V →ₗ[ℂ] W, ∀ x : Fin n → X,
      L (symMonomial n V (fun i => s (x i))) = F x := by sorry
