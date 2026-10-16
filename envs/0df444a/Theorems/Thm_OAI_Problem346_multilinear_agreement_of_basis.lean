-- Prove2me | Theorems.Thm_OAI_Problem346_multilinear_agreement_of_basis
-- name    : OAI.Problem346.multilinear_agreement_of_basis
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:20:54.381767+00:00
-- url     : https://prove2.me/theorems/64c449e8-0664-4e55-813d-b5e64ab84115
-- title:
--   A separately linear function that agrees with a multilinear map on basis tuples agrees with it everywhere
-- statement:
--   Let $R$ be a field, $I$ a finite index set and $W$ a vector space over $R$. For each $i\in I$ suppose given:
--
--   - an $R$-vector space $M_i$, a set $X_i$ and a map $s_i\colon X_i\to M_i$;
--   - a basis $(B_{i,k})_{k\in K_i}$ of $M_i$ and a map $t_i\colon K_i\to X_i$ with $s_i(t_i(k))=B_{i,k}$ for every $k\in K_i$.
--
--   Thus every basis vector has a chosen preimage under $s_i$. For $x=(x_i)_{i\in I}\in\prod_{i}X_i$, an index $i$ and $y\in X_i$, write $x[i\leftarrow y]$ for the family obtained from $x$ by replacing its $i$-th entry with $y$. Let $F\colon\prod_{i\in I}X_i\to W$ be any function and $G\colon\prod_{i\in I}M_i\to W$ an $R$-multilinear map. Assume:
--
--   1. (separate linearity of $F$ through $s$) for every $x\in\prod_iX_i$ and every $i\in I$ there is an $R$-linear map $L\colon M_i\to W$ with $L(s_i(y))=F(x[i\leftarrow y])$ for all $y\in X_i$;
--   2. (agreement on basis tuples) $F\bigl((t_i(k_i))_{i\in I}\bigr)=G\bigl((B_{i,k_i})_{i\in I}\bigr)$ for every $k\in\prod_iK_i$.
--
--   **Theorem.** Then
--
--   $$
--   F(x)=G\bigl((s_i(x_i))_{i\in I}\bigr)\qquad\text{for every }x\in\prod_{i\in I}X_i .
--   $$
--
--   The function $F$ is only given on generators, and the theorem identifies it with a genuine multilinear map. This is the uniqueness half of the construction of multilinear maps from formulas on generators. Defining $G$ on a tensor-product basis supplies existence, and this is how a symmetric formula on products of monomials is turned into a linear map on a symmetric power.
--
--   **Formalization Note** The index types $X_i$ and $K_i$ are arbitrary types, and $x[i\leftarrow y]$ is `Function.update x i y`, which is why `DecidableEq I` is assumed along with `Fintype I`. The bases are Mathlib `Basis (K i) R (M i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SpanningAgreement.lean#L11-L59

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
open scoped BigOperators
open Module

theorem OAI.Problem346.multilinear_agreement_of_basis
    {R I W : Type*} [Field R] [Fintype I] [DecidableEq I]
    {M X K : I → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [AddCommGroup W] [Module R W]
    (s : ∀ i, X i → M i) (B : ∀ i, Basis (K i) R (M i))
    (t : ∀ i, K i → X i) (ht : ∀ i k, s i (t i k) = B i k)
    (F : (∀ i, X i) → W) (G : MultilinearMap R M W)
    (hlinear : ∀ x : ∀ i, X i, ∀ i,
      ∃ L : M i →ₗ[R] W, ∀ y, L (s i y) = F (Function.update x i y))
    (hbase : ∀ k : ∀ i, K i, F (fun i => t i (k i)) = G (fun i => B i (k i))) :
    ∀ x : ∀ i, X i, F x = G (fun i => s i (x i)) := by sorry
