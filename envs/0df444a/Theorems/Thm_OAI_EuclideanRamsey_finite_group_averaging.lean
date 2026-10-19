-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_finite_group_averaging
-- name    : OAI.EuclideanRamsey.finite_group_averaging
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:44:41.319982+00:00
-- url     : https://prove2.me/theorems/ce381519-7b12-412c-8416-e65f9432bce3
-- title:
--   Finite group averaging makes orbit differences deep in the derived series and cheap
-- statement:
--   Let $G$ be a group, $N\trianglelefteq G$ a normal subgroup, and $N^{(0)}=N$, $N^{(k+1)}=[N^{(k)},N^{(k)}]$ its derived series (each $N^{(k)}$ is normal in $G$). Fix $r\in\mathbb{N}$ and a *normal cost* $\kappa$ on $N^{(r)}$: a function $\kappa:G\to\mathbb{R}$ with $\kappa\ge0$, $\kappa(1)=0$, and $\kappa(g^{-1})=\kappa(g)$, $\kappa(kgk^{-1})=\kappa(g)$, $\kappa(gh)\le\kappa(g)+\kappa(h)$ for all $g,h\in N^{(r)}$ and $k\in G$.
--
--   Let a finite group $H$ act on a finite set $X$; points $x,y\in X$ are in the same orbit if $y=h\cdot x$ for some $h\in H$. Let $\ell:X\to G$ (the "letters") satisfy $\ell(x)\,\ell(y)^{-1}\in N$ for all $x,y\in X$. A map $w:X\to G$ is an *orbit word of length $m$* over $\ell$ if this follows from the rules: every constant map has length $0$; for each $h\in H$ the translated letter map $x\mapsto\ell(h\cdot x)$ has length $1$; and the pointwise product of orbit words of lengths $m$ and $m'$ has length $m+m'$.
--
--   **Theorem.** For every real $\delta>0$ there are a map $w:X\to G$ and an integer $m>0$ such that $w$ is an orbit word of length $m$ over $\ell$ and, for all $x,y$ in the same $H$-orbit,
--
--   $$
--   w(x)\,w(y)^{-1}\in N^{(r)}\qquad\text{and}\qquad \kappa\bigl(w(x)\,w(y)^{-1}\bigr)\le\delta\,m .
--   $$
--
--   So suitable products of translated letters have all their differences along orbits arbitrarily deep in the derived series of $N$ and arbitrarily cheap relative to their length. In the Euclidean Ramsey classification this averaging step, with $H$ a permutation group, is used to build word families that admit paths of very different weights.
--
--   **Formalization Note** The derived series is `Derived N r`, the cost is a structure `NormalCost (Derived N r)`, orbit words are the inductive predicate `OrbitWords letter w m`, and being in the same orbit is `SameOrbit x y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean#L289-L306

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging

open OAI OAI.EuclideanRamsey
universe uGroup uAction uPoint
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct BigOperators
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped BigOperators RealInnerProductSpace
open Filter
open Set
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H] [Fintype X]

theorem OAI.EuclideanRamsey.finite_group_averaging (N : Subgroup G) [N.Normal] (r : ℕ)
    (c : NormalCost (Derived N r)) (letter : X → G)
    (hletter : ∀ x y,letter x*(letter y)⁻¹∈N) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (w : X → G) (m : ℕ),OrbitWords (H:=H) letter w m ∧ 0 < m ∧
      ∀ x y,SameOrbit (H:=H) x y →
        w x*(w y)⁻¹∈Derived N r ∧ c.cost (w x*(w y)⁻¹)≤δ*m := by sorry
