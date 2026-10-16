-- Prove2me | Theorems.Thm_OAI_Problem346_IsFoulkesMap_surjective_of_vanishing
-- name    : OAI.Problem346.IsFoulkesMap.surjective_of_vanishing
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:26:58.169567+00:00
-- url     : https://prove2.me/theorems/2f41436a-a28e-4d3c-a9f2-21d476b5cb20
-- title:
--   Diagonal vanishing of symmetric forms on $\operatorname{Sym}^bV$ forces every Foulkes map to be surjective
-- statement:
--   Let $V$ be a complex vector space of arbitrary dimension and let $a,b\in\mathbb{N}$. Write $\operatorname{Sym}(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\operatorname{Sym}^nV\subseteq\operatorname{Sym}(V)$ be the complex linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$. For $n=0$ this is the span of the empty product $1$. For $(v_0,\dots,v_{n-1})\in V^n$ write $[v_0,\dots,v_{n-1}]=v_0\cdots v_{n-1}\in\operatorname{Sym}^nV$ and call it a monomial. Applying the construction to the spaces $\operatorname{Sym}^aV$ and $\operatorname{Sym}^bV$ gives $\operatorname{Sym}^b(\operatorname{Sym}^aV)$ and $\operatorname{Sym}^a(\operatorname{Sym}^bV)$. Let $S_a$ be the group of permutations of $\{0,\dots,a-1\}$. For an array $v=(v_{j,i})$ of vectors of $V$ with $0\le j<b$ and $0\le i<a$, put
--
--   $$
--   \Phi(v)=\frac{1}{(a!)^{b}}\sum_{(\sigma_0,\dots,\sigma_{b-1})\in S_a^{\,b}}\Bigl[\,[v_{0,\sigma_0(0)},\dots,v_{b-1,\sigma_{b-1}(0)}],\ \dots,\ [v_{0,\sigma_0(a-1)},\dots,v_{b-1,\sigma_{b-1}(a-1)}]\,\Bigr]\in\operatorname{Sym}^a(\operatorname{Sym}^bV).
--   $$
--
--   A $\mathbb{C}$-linear map $\mu\colon\operatorname{Sym}^b(\operatorname{Sym}^aV)\to\operatorname{Sym}^a(\operatorname{Sym}^bV)$ is a *Foulkes map* if $\mu\bigl([\,[v_{0,0},\dots,v_{0,a-1}],\dots,[v_{b-1,0},\dots,v_{b-1,a-1}]\,]\bigr)=\Phi(v)$ for every such array $v$. A *symmetric $a$-linear form on $\operatorname{Sym}^bV$* is a multilinear map $T\colon(\operatorname{Sym}^bV)^a\to\mathbb{C}$ with $T(P_{\sigma(0)},\dots,P_{\sigma(a-1)})=T(P_0,\dots,P_{a-1})$ for all $\sigma\in S_a$.
--
--   **Theorem.** Assume the diagonal vanishing criterion: every symmetric $a$-linear form $T$ on $\operatorname{Sym}^bV$ with
--
--   $$
--   T(P,P,\dots,P)=0\qquad\text{for every monomial }P=[u_0,\dots,u_{b-1}],\ u_0,\dots,u_{b-1}\in V,
--   $$
--
--   is identically zero. Then every Foulkes map $\mu$ is surjective.
--
--   This reduces surjectivity of the Foulkes map, a statement about the plethysm spaces, to a vanishing statement about symmetric multilinear forms, which is established separately for finite-dimensional $V$ under the quadratic bound $a(a-1)\le b$. Together with the existence and uniqueness of Foulkes maps, it shows that whenever the criterion holds there is exactly one Foulkes map and it is surjective. The argument is pure duality and needs no finite-dimensionality of $V$.
--
--   **Formalization Note** $\operatorname{Sym}^nV$ is `SymPow n V`, the subtype of the submodule `symPowSubmodule n V` of Mathlib's `SymmetricAlgebra ℂ V`, and $[v_0,\dots,v_{n-1}]$ is `symMonomial n V v`. The Foulkes condition is `IsFoulkesMap a b V μ`, with $\Phi$ given by `foulkesFormula`. The type `SymmetricMultilinearForm a b V` consists of all multilinear maps $(\operatorname{Sym}^bV)^a\to\mathbb{C}$, and symmetry is the separate predicate `IsSymmetricMultilinearForm a b V T`. The diagonal argument $(P,\dots,P)$ is the constant tuple `fun _ => symMonomial b V u`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Annihilator.lean#L12-L34

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

theorem OAI.Problem346.IsFoulkesMap.surjective_of_vanishing (a b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V]
    (μ : SymPow b (SymPow a V) →ₗ[ℂ] SymPow a (SymPow b V))
    (hμ : IsFoulkesMap a b V μ)
    (hvan : ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ u : Fin b → V, T (fun _ => symMonomial b V u) = 0) → T = 0) :
    Function.Surjective μ := by sorry
