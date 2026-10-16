-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_exists_positive_ge
-- name    : OAI.CliqueFreeIndependence.FiniteCoupling.exists_positive_ge
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:56:55.674481+00:00
-- url     : https://prove2.me/theorems/cd38e50b-746a-469f-836c-303e149f252b
-- title:
--   Some outcome of positive probability is at least the mean
-- statement:
--   Let $I$ be a finite set, let $q$ be a probability distribution on $I$ ($q_i\ge0$ for all $i$ and $\sum_{i\in I}q_i=1$), let $f:I\to\mathbb{R}$, and let $L$ be a real number with
--
--   $$
--   L\le\sum_{i\in I}q_i\,f(i).
--   $$
--
--   Then there exists $i\in I$ with $q_i>0$ and $f(i)\ge L$.
--
--   This is the first-moment principle of the probabilistic method: if a random variable has expectation at least $L$, then some outcome that occurs with positive probability has value at least $L$. Requiring $q_i>0$ keeps the chosen outcome in the support, so that every property that holds for all outcomes of positive probability also holds for it. It converts an averaged bound over a random construction into a specific deterministic choice.
--
--   **Formalization Note** The distribution is a real vector `q` with `Law q` (nonnegative entries summing to $1$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean#L356-L373

import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical
import Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
import Definitions.Def_OAI_Combinatorics_CliqueFree_Optimizer
import Definitions.Def_OAI_Combinatorics_CliqueFree_Lottery
import Definitions.Def_OAI_Combinatorics_CliqueFree_MultiplierLaw
import Definitions.Def_OAI_Combinatorics_CliqueFree_Deletion
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_EdgeState
import Definitions.Def_OAI_Combinatorics_CliqueFree_SparseMultipliers
import Definitions.Def_OAI_Combinatorics_CliqueFree_TriangleState
import Definitions.Def_OAI_Combinatorics_CliqueFree_Projection
import Definitions.Def_OAI_Combinatorics_CliqueFree_Splitting
import Definitions.Def_OAI_Combinatorics_CliqueFree_Reach
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteKernel
import Definitions.Def_OAI_Combinatorics_CliqueFree_LocalWalk
import Definitions.Def_OAI_Combinatorics_CliqueFree_WalkEntropy
import Definitions.Def_OAI_Combinatorics_CliqueFree_FiniteCoupling

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteCoupling
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
universe z
variable {I : Type u} {J : Type v} {E : Type z}
variable [Fintype I] [Fintype J] [Fintype E]
private noncomputable local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I
private noncomputable local instance instDecidableEq_oAI_1 : DecidableEq J := Classical.decEq J
attribute [local instance] OAI.CliqueFreeIndependence.FiniteCoupling.instDecidableEq_oAI_2

theorem OAI.CliqueFreeIndependence.FiniteCoupling.exists_positive_ge {q : I → ℝ} (hq : Law q) (f : I → ℝ) {L : ℝ}
    (hL : L ≤ ∑ i, q i * f i) : ∃ i, 0 < q i ∧ L ≤ f i := by sorry
