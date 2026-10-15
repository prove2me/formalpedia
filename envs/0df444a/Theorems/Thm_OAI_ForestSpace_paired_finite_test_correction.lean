-- Prove2me | Theorems.Thm_OAI_ForestSpace_paired_finite_test_correction
-- name    : OAI.ForestSpace.paired_finite_test_correction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T04:15:42.279016+00:00
-- url     : https://prove2.me/theorems/3fe35e01-0637-4230-b1cf-0d3b6c55f316
-- title:
--   One gate correction for both signs: paired segment tests with squared norm $1+12s^2$ on a finite forest
-- statement:
--   Let $V$ be a finite partially ordered set that is a *forest*: whenever $a\le c$ and $b\le c$, the elements $a$ and $b$ are comparable. A *segment* is a finite chain $S\subseteq V$ that is order-convex; for $u:V\to\mathbb{R}$ write $u(S)=\sum_{v\in S}u(v)$ and
--   $$
--   \|u\|_{\mathrm{seg}}^2=\sup\Bigl\{\sum_{i\in I}u(S_i)^2\ :\ (S_i)_{i\in I}\ \text{a finite family of pairwise disjoint segments}\Bigr\}.
--   $$
--
--   **Theorem.** Let $H\subseteq V$ be a lower set and let $f,k:V\to\mathbb{R}$ satisfy $f(v)=0$ for all $v\notin H$ and $k(v)=0$ for all $v\in H$, with $\|f\|_{\mathrm{seg}}^2\le1$ and $\|k\|_{\mathrm{seg}}^2\le1$. Let $s>0$. Then there is $c:V\to\mathbb{R}$ with $c(v)=0$ for all $v\in H$ and $\|c\|_{\mathrm{seg}}^2\le1$ such that
--   $$
--   \|f+s(c+k)\|_{\mathrm{seg}}^2\le1+12s^2\qquad\text{and}\qquad\|f+s(c-k)\|_{\mathrm{seg}}^2\le1+12s^2 .
--   $$
--
--   The triangle inequality alone only gives $\|f\pm sk\|_{\mathrm{seg}}\le1+s$, and $(1+s)^2=1+2s+s^2$ exceeds $1+12s^2$ whenever $0<s<2/11$. The point is that a single correction $c$, living on the complement of $H$, achieves the better bound for both signs at once; when a dual pair $x,y$ (with $x$ blind to the complement of $H$ and $y$ blind to $H$) is evaluated on these two vectors and the results are averaged, the contributions of $c$ cancel. This is the finite combinatorial core of the dual estimate $\sqrt{\|x\|^2+\|y\|^2/12}\le\tfrac12\bigl(\|x+y\|+\|x-y\|\bigr)$ in the forest space.
--
--   **Formalization Note** The bounds $\|u\|_{\mathrm{seg}}^2\le C$ are stated as `TestBound u C`, `V` carries a `Fintype` instance, and the forest condition is `ForestOrder V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Paired.lean#L175-L195

import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired

open OAI OAI.ForestSpace
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [PartialOrder V]

theorem OAI.ForestSpace.paired_finite_test_correction
    (hF : ForestOrder V) (H : Set V) (hH : IsLowerSet H) (f k : V → ℝ)
    (hf : ∀ v, v ∉ H → f v = 0) (hk : ∀ v, v ∈ H → k v = 0)
    (hf₁ : TestBound f 1) (hk₁ : TestBound k 1)
    (s : ℝ) (hs : 0 < s) :
    ∃ c : V → ℝ, (∀ v, v ∈ H → c v = 0) ∧ TestBound c 1 ∧
      TestBound (f + s • (c + k)) (1 + 12 * s ^ 2) ∧
      TestBound (f + s • (c - k)) (1 + 12 * s ^ 2) := by sorry
