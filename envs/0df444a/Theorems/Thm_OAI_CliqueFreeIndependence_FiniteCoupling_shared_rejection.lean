-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_shared_rejection
-- name    : OAI.CliqueFreeIndependence.FiniteCoupling.shared_rejection
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:53:59.92677+00:00
-- url     : https://prove2.me/theorems/caa622c0-a63e-407d-ae2e-2af8a0f954cf
-- title:
--   Shared rejection coupling with disagreement probability at most $2d/(1+d)$
-- statement:
--   Let $I$ and $J$ be finite sets with $J$ nonempty, and for each $i\in I$ let $p_i$ be a probability distribution on $J$. For $i,j\in I$ let
--
--   $$
--   d_{ij}=\frac12\sum_{y\in J}\big|p_i(y)-p_j(y)\big|
--   $$
--
--   be the total variation distance between $p_i$ and $p_j$. Then there is a probability distribution $q$ on the set of functions $F:I\to J$ such that, for all $i,j\in I$ and $y\in J$,
--
--   $$
--   \sum_{F:\ F(i)=y}q(F)=p_i(y)\qquad\text{and}\qquad\sum_{F:\ F(i)\ne F(j)}q(F)\le\frac{2\,d_{ij}}{1+d_{ij}} .
--   $$
--
--   So the whole family $(p_i)_{i\in I}$ can be coupled by one random function $\mathbf F$ with $\mathbf F(i)\sim p_i$, in such a way that every pair of coordinates disagrees with probability at most $2d_{ij}/(1+d_{ij})\le2d_{ij}$; for a single pair the smallest possible value would be $d_{ij}$, but here the bound holds for all pairs simultaneously. This makes it possible to replace the rows of a Markov kernel by one random choice function whose disagreement probabilities are controlled by the total variation distances between rows.
--
--   **Formalization Note** $d_{ij}$ is `dist (p i) (p j)` from the coupling namespace (half the $\ell^1$ distance, not a metric-space distance), and laws are real vectors satisfying `Law`. The name refers to the construction: one shared uniform-threshold set per label, followed by first-accepted-trial assignment.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean#L272-L334

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

theorem OAI.CliqueFreeIndependence.FiniteCoupling.shared_rejection [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤
        2 * dist (p i) (p j) / (1 + dist (p i) (p j))) := by sorry
