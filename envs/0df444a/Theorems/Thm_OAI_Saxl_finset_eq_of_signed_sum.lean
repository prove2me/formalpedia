-- Prove2me | Theorems.Thm_OAI_Saxl_finset_eq_of_signed_sum
-- name    : OAI.Saxl.finset_eq_of_signed_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T23:54:19.748174+00:00
-- url     : https://prove2.me/theorems/99874fa2-858a-4a8a-b827-dbbe2de68c6e
-- title:
--   A finite set is the unique maximizer of a weight that is positive exactly on it
-- statement:
--   Let $X$ be a type with decidable equality, let $A,B\subseteq X$ be finite sets, and let $w:X\to\mathbb{Z}$ be a weight that is strictly positive on $B$ and strictly negative off $B$:
--   $$w(x)>0\ \ (x\in B),\qquad w(x)<0\ \ (x\notin B).$$
--   If the total weights agree,
--   $$\sum_{x\in A}w(x)=\sum_{x\in B}w(x),$$
--   then $A=B$.
--
--   Equivalently, among all finite subsets of $X$, $B$ is the unique one maximizing $A\mapsto\sum_{x\in A}w(x)$. This equality-case rigidity identifies a set of cells with a given shape from linear statistics alone: one chooses a weight such as $2\mu_r-2c-1$ (positive exactly on the cells $(r,c)$ of a Young diagram $\mu$ with row lengths $\mu_r$) or $2h-1-2i-2j$ (positive exactly on the staircase $\{i+j<h\}$) and checks that the two weight sums coincide.
--
--   **Formalization Note** The sets are `Finset X` and the weight takes integer values; no finiteness of `X` itself is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/Polytabloid.lean#L15-L44

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX

theorem OAI.Saxl.finset_eq_of_signed_sum {X : Type uX} [DecidableEq X]
    (A B : Finset X) (w : X → ℤ)
    (hp : ∀ x ∈ B, 0 < w x) (hn : ∀ x ∉ B, w x < 0)
    (he : ∑ x ∈ A, w x = ∑ x ∈ B, w x) : A = B := by sorry
