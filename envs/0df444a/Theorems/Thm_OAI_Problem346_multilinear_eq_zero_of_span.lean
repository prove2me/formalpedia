-- Prove2me | Theorems.Thm_OAI_Problem346_multilinear_eq_zero_of_span
-- name    : OAI.Problem346.multilinear_eq_zero_of_span
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:16:53.260154+00:00
-- url     : https://prove2.me/theorems/37d30a39-1c6d-4d33-8ac7-1e7a0acca4ec
-- title:
--   A multilinear map that vanishes on all tuples from a spanning set is zero
-- statement:
--   Let $M$ and $N$ be complex vector spaces and let $s\subseteq M$ be a subset whose complex linear span is all of $M$.
--
--   **Theorem.** For every $n\in\mathbb{N}$ and every $n$-multilinear map $F\colon M^n\to N$ (that is, $F$ is $\mathbb{C}$-linear in each of its $n$ arguments separately), if
--
--   $$
--   F(x_0,\dots,x_{n-1})=0\qquad\text{whenever }x_0,\dots,x_{n-1}\in s,
--   $$
--
--   then $F=0$.
--
--   For $n=0$ the map $F$ is a constant, and the hypothesis says that this constant is $0$. Applied to a difference $F-G$, the theorem says that two multilinear maps that agree on all tuples from a spanning set are equal. This extensionality principle is used to determine linear maps on iterated symmetric powers by their values on products of monomials, and to show that a multilinear extension of a symmetric formula is itself symmetric.
--
--   **Formalization Note** $F$ ranges over `MultilinearMap ℂ (fun _ : Fin n => M) N`. The spanning hypothesis is `Submodule.span ℂ s = ⊤`, and the theorem quantifies over $n$ before $F$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Spanning.lean#L26-L50

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

theorem OAI.Problem346.multilinear_eq_zero_of_span
    {M : Type u} [AddCommGroup M] [Module ℂ M]
    {N : Type v} [AddCommGroup N] [Module ℂ N]
    {s : Set M} (hs : Submodule.span ℂ s = ⊤) (n : ℕ) :
    ∀ F : MultilinearMap ℂ (fun _ : Fin n => M) N,
      (∀ x, (∀ i, x i ∈ s) → F x = 0) → F = 0 := by sorry
