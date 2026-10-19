-- Prove2me | Theorems.Thm_OAI_DiamondDistortion_Ancestry_finite_heads_of_predecessors
-- name    : OAI.DiamondDistortion.Ancestry.finite_heads_of_predecessors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:58:34.083915+00:00
-- url     : https://prove2.me/theorems/4fee15a2-c212-4931-8553-1c050266af09
-- title:
--   Finitely many ancestors per vertex give an exhaustion by finite ancestral sets
-- statement:
--   Let $V$ be a set carrying an *ancestry*: a partial order $\le$ (read $a\le b$ as "$a$ is an ancestor of $b$") in which the ancestors of every vertex form a chain, i.e. $a\le c$ and $b\le c$ imply $a\le b$ or $b\le a$. A set $K\subseteq V$ is *ancestral* if $a\le b$ and $b\in K$ imply $a\in K$.
--
--   If every vertex has only finitely many ancestors, i.e. the set $\{a\in V:\ a\le b\}$ is finite for every $b\in V$, then every finite set is contained in a finite ancestral set:
--
--   $$
--   \text{for every finite }S\subseteq V\text{ there is a finite }K\subseteq V\text{ with }S\subseteq K\text{ and }K\text{ ancestral}.
--   $$
--
--   This exhaustion property is the standing hypothesis of the intrinsic tail estimates in the dual of the segment-norm space. The lemma shows that it holds whenever every vertex has finite depth, for example in the tree of finite words over $\mathbb{N}$ ordered by the prefix relation.
--
--   **Formalization Note** The vertex set is a type with an `Ancestry` instance; the finiteness hypothesis is `({a : ι | a ≤ b} : Set ι).Finite` for all `b`, and the finite sets are `Finset`s.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DiamondDistortion/Ancestry.lean#L1185-L1199

import Mathlib
import Definitions.Def_DiamondDistortion
import Definitions.Def_OAI_Analysis_DiamondDistortion_SegmentNorm
import Definitions.Def_OAI_Analysis_DiamondDistortion_Ancestry

open OAI OAI.DiamondDistortion OAI.DiamondDistortion.Ancestry
universe u v
open scoped BigOperators Classical Topology
open Set
open scoped Classical
attribute [local instance] OAI.DiamondDistortion.Ancestry.instPartialOrder
variable {ι : Type*} [A : Ancestry ι]

theorem OAI.DiamondDistortion.Ancestry.finite_heads_of_predecessors
    (hpred : ∀ b : ι, ({a : ι | a ≤ b} : Set ι).Finite) :
    ∀ S : Finset ι, ∃ K : Finset ι, S ⊆ K ∧ A.Ancestral (K : Set ι) := by sorry
