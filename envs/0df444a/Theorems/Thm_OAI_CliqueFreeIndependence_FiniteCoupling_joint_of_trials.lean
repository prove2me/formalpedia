-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteCoupling_joint_of_trials
-- name    : OAI.CliqueFreeIndependence.FiniteCoupling.joint_of_trials
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:51:55.679753+00:00
-- url     : https://prove2.me/theorems/e25e6e8d-6998-45e2-84ad-27501ba04d9b
-- title:
--   First-accepted-trial coupling with prescribed marginals and disagreement bounds
-- statement:
--   Let $I$, $J$ and $E$ be finite sets with $J$ nonempty, and for each $i\in I$ let $p_i$ be a probability distribution on $J$ ($p_i(y)\ge0$ and $\sum_{y\in J}p_i(y)=1$). Suppose that each *trial* $e\in E$ carries a weight $t_e\ge0$, an acceptance set $A_e\subseteq I$ and a label $\ell_e\in J$, and that the trials reproduce the marginals:
--
--   $$
--   \sum_{e\in E:\ i\in A_e,\ \ell_e=y}t_e=p_i(y)\qquad\text{for all }i\in I,\ y\in J .
--   $$
--
--   (Summing over $y$ shows that the trials accepting $i$ have total weight $1$.) Let $D:I\times I\to\mathbb{R}$ be such that for all $i,j\in I$
--
--   $$
--   \sum_{e:\ \text{exactly one of }i,j\text{ lies in }A_e}t_e\;\le\;D(i,j)\sum_{e:\ i\in A_e\text{ or }j\in A_e}t_e .
--   $$
--
--   Then there is a probability distribution $q$ on the set of functions $F:I\to J$ such that, for all $i,j\in I$ and $y\in J$,
--
--   $$
--   \sum_{F:\ F(i)=y}q(F)=p_i(y)\qquad\text{and}\qquad\sum_{F:\ F(i)\ne F(j)}q(F)\le D(i,j).
--   $$
--
--   Thus a random function $\mathbf F$ with law $q$ couples all the distributions $p_i$ at once ($\mathbf F(i)\sim p_i$), while any two coordinates disagree with probability at most $D(i,j)$. The intuition is the first-accepted-trial scheme: draw trials independently with probabilities proportional to $t$, and give each $i$ the label of the first trial whose acceptance set contains $i$. Then $\mathbf F(i)$ and $\mathbf F(j)$ can differ only if the first trial meeting $\{i,j\}$ contains exactly one of them, an event whose probability is the ratio bounded in the hypothesis. The theorem is an exact finite version of this construction.
--
--   **Formalization Note** Distributions are real vectors satisfying `Law` (nonnegative entries summing to $1$); "exactly one of $i,j$ lies in $A_e$" is written `Xor (i ∈ A e) (j ∈ A e)`, and all probabilities are sums of `if … then … else 0`. The nonemptiness of $J$ is the instance `[Nonempty J]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteCoupling.lean#L130-L265

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

theorem OAI.CliqueFreeIndependence.FiniteCoupling.joint_of_trials [Nonempty J] (p : I → J → ℝ) (hp : ∀ i, Law (p i))
    (t : E → ℝ) (ht : ∀ e, 0 ≤ t e) (A : E → Finset I) (label : E → J)
    (hmarg : ∀ i y, (∑ e, if i ∈ A e ∧ label e = y then t e else 0) = p i y)
    (D : I → I → ℝ)
    (hpair : ∀ i j,
      (∑ e, if Xor (i ∈ A e) (j ∈ A e) then t e else 0) ≤
        D i j * (∑ e, if i ∈ A e ∨ j ∈ A e then t e else 0)) :
    ∃ q : (I → J) → ℝ, Law q ∧
      (∀ i y, (∑ f, if f i = y then q f else 0) = p i y) ∧
      (∀ i j, (∑ f, if f i ≠ f j then q f else 0) ≤ D i j) := by sorry
