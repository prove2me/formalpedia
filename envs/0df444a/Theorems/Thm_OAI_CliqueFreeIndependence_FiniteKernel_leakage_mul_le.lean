-- Prove2me | Theorems.Thm_OAI_CliqueFreeIndependence_FiniteKernel_leakage_mul_le
-- name    : OAI.CliqueFreeIndependence.FiniteKernel.leakage_mul_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:40:40.747177+00:00
-- url     : https://prove2.me/theorems/6cce160f-a66b-416d-bc8a-a056621da96f
-- title:
--   Two-step leakage bound for a product of stochastic kernels
-- statement:
--   Let $I$ be a finite set. A *kernel* on $I$ is a real matrix $K=(K(i,j))_{i,j\in I}$; it is *stochastic* if every row is a probability vector, i.e. $K(i,j)\ge 0$ and $\sum_{j\in I}K(i,j)=1$ for every $i$. For a kernel $K$, a state $i\in I$ and a set $A\subseteq I$ write $K(i,A)=\sum_{j\in A}K(i,j)$ for the row mass of $A$, write $A^{c}=I\setminus A$, and let $PQ$ be the matrix product, $(PQ)(i,y)=\sum_{z\in I}P(i,z)\,Q(z,y)$.
--
--   Let $P$ and $Q$ be stochastic kernels on $I$, let $i\in I$ and let $A,B\subseteq I$. Then
--
--   $$
--   (PQ)(i,B^{c})\;\le\;P(i,A^{c})\;+\;\sum_{y\in B^{c}}\sum_{z\in A}P(i,z)\,Q(z,y).
--   $$
--
--   In probabilistic terms: for a two-step chain $i\to Z\to Y$ whose first step is drawn from $P(i,\cdot)$ and whose second step is drawn from $Q(Z,\cdot)$, the probability of ending outside $B$ is at most the probability that the first step leaves $A$, plus the probability that the first step lands in $A$ and the second step then leaves $B$. Applied along a growing sequence of target sets, the inequality accumulates the "leakage" of a random walk one step at a time; this is how one shows that a smoothed walk stays, up to a small error, inside an increasing family of sets.
--
--   **Formalization Note** Kernels are `Kernel I = Matrix I I ℝ`, stochasticity is `Stochastic`, and $K(i,A)$ is `rowMass K i A`; the sets $A,B$ are `Finset`s and complements are taken in the finite type $I$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/FiniteKernel.lean#L370-L386

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

open OAI OAI.CliqueFreeIndependence OAI.CliqueFreeIndependence.FiniteKernel
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable
universe u v
open FiniteEntropy
variable {I : Type u} [Fintype I]
variable {J : Type v}
attribute [local instance] OAI.CliqueFreeIndependence.FiniteKernel.instDecidableEq_oAI

theorem OAI.CliqueFreeIndependence.FiniteKernel.leakage_mul_le {P Q : Kernel I} (hP : Stochastic P) (hQ : Stochastic Q)
    (i : I) (A B : Finset I) :
    rowMass (P * Q) i Bᶜ ≤ rowMass P i Aᶜ + ∑ y ∈ Bᶜ, ∑ z ∈ A, P i z * Q z y := by sorry
