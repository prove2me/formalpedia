-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_exists_threshold_law
-- name    : OAI.CliqueFreeIndependence.FiniteCoupling.exists_threshold_law
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:49:27.559771+00:00
-- url     : https://prove2.me/theorems/1b927908-bc49-49da-b1a5-9e1c724f13ef
-- title:
--   Threshold coupling: a random set with inclusion probabilities $a_i$ and pairwise inclusion $\min(a_i,a_j)$
-- statement:
--   Let $I$ be a finite set and let $a:I\to\mathbb{R}$ satisfy $0\le a_i\le1$ for every $i\in I$. Then there is a probability distribution $q$ on the subsets of $I$, that is $q(A)\ge0$ for every $A\subseteq I$ and $\sum_{A\subseteq I}q(A)=1$, such that for all $i,j\in I$
--
--   $$
--   \sum_{A\subseteq I,\ A\ni i}q(A)=a_i\qquad\text{and}\qquad\sum_{A\subseteq I,\ A\ni i,\,j}q(A)=\min\{a_i,a_j\}.
--   $$
--
--   Equivalently, there is a random subset $\mathbf S\subseteq I$ with $\Pr(i\in\mathbf S)=a_i$ and $\Pr(i\in\mathbf S\text{ and }j\in\mathbf S)=\min\{a_i,a_j\}$ for all $i,j$. The inclusion events are therefore nested, and the indicators of $i\in\mathbf S$ are coupled as positively as possible; such a set is obtained from a single uniform threshold $U\in[0,1]$ as $\mathbf S=\{i: U\le a_i\}$. One such threshold set per label is the building block of the shared rejection coupling of several probability distributions.
--
--   **Formalization Note** The distribution is a function `q : Finset I → ℝ` with `Law q` (nonnegative entries with total sum $1$), and each probability is written as the sum of `q A` over the subsets `A` in the event.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean#L76-L128

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

open MeasureTheory in
theorem OAI.CliqueFreeIndependence.FiniteCoupling.exists_threshold_law (a : I → ℝ) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∀ i, a i ≤ 1) :
    ∃ q : Finset I → ℝ, Law q ∧
      (∀ i, (∑ A, if i ∈ A then q A else 0) = a i) ∧
      (∀ i j, (∑ A, if i ∈ A ∧ j ∈ A then q A else 0) = min (a i) (a j)) := by sorry
