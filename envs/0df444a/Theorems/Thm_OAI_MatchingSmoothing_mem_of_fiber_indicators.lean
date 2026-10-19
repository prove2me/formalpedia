-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_mem_of_fiber_indicators
-- name    : OAI.MatchingSmoothing.mem_of_fiber_indicators
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:29:10.443778+00:00
-- url     : https://prove2.me/theorems/71648b0b-d210-4aac-b84b-fd00f7eef629
-- title:
--   Functions constant on the fibres of a finite-valued map lie in any subspace containing the fibre indicators
-- statement:
--   Let $X$ be an arbitrary set, $I$ a finite set and $\theta:X\to I$ a map. Let $S$ be a linear subspace of the real vector space $\mathbb R^X$ of all functions $X\to\mathbb R$. Suppose $S$ contains the indicator function of every nonempty fibre of $\theta$:
--
--   $$
--   \mathbf 1_{\{b\in X:\ \theta(b)=\theta(a)\}}\in S\qquad\text{for every }a\in X .
--   $$
--
--   Let $f:X\to\mathbb R$ be constant on the fibres of $\theta$, i.e. $\theta(a)=\theta(b)$ implies $f(a)=f(b)$. Then $f\in S$.
--
--   The fibre-constant functions are exactly the functions that factor through $\theta$. The lemma says that every such function is a finite linear combination of fibre indicators, so membership in $S$ only needs to be checked on those indicators. It is used to show that a function on perfect matchings that depends only on a finite combinatorial invariant (such as the set of edges a matching has inside a fixed vertex set) is a low-degree polynomial in the edge indicators: it is enough to show this for the indicator of each value of the invariant.
--
--   **Formalization Note** $X$ need not be finite; only the codomain $I$ is a `Fintype`, and this makes the representing sum finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/EdgeProducts.lean#L66-L92

import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts

open OAI OAI.MatchingSmoothing
universe u_1 u_2 u_3 u_4
variable {E : Type u_1} {X : Type u_2}

theorem OAI.MatchingSmoothing.mem_of_fiber_indicators {I : Type u_4} [Fintype I] [DecidableEq I]
    (θ : X → I) (f : X → ℝ) (S : Submodule ℝ (X → ℝ))
    (hf : ∀ a b, θ a = θ b → f a = f b)
    (hind : ∀ a, (fun b => if θ b = θ a then (1 : ℝ) else 0) ∈ S) : f ∈ S := by sorry
