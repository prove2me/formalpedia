-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_NormalCost_product_difference
-- name    : OAI.EuclideanRamsey.NormalCost.product_difference
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:39:53.656983+00:00
-- url     : https://prove2.me/theorems/381d10c4-6abf-431c-937a-602c1f5d1072
-- title:
--   The normal cost of a quotient of two products is at most the sum of the factorwise costs
-- statement:
--   Let $G$ be a group and $L\trianglelefteq G$ a normal subgroup. A *normal cost* on $L$ is a function $\kappa:G\to\mathbb{R}$ such that $\kappa(g)\ge0$ for all $g\in G$, $\kappa(1)=0$, and for all $g,h\in L$ and $k\in G$
--   $$\kappa(g^{-1})=\kappa(g),\qquad \kappa(kgk^{-1})=\kappa(g),\qquad \kappa(gh)\le\kappa(g)+\kappa(h),$$
--   that is, a conjugation-invariant length function, with the axioms required only on $L$.
--
--   **Theorem.** Let $\kappa$ be a normal cost on $L$, let $j_1,\dots,j_n$ be a finite list of elements of an index set $\alpha$ (repetitions allowed), and let $a,b:\alpha\to G$ satisfy $a(j)\,b(j)^{-1}\in L$ for every $j$ in the list. Write $A=a(j_1)a(j_2)\cdots a(j_n)$ and $B=b(j_1)b(j_2)\cdots b(j_n)$. Then:
--
--   1. the quotient $AB^{-1}$ lies in $L$;
--   2. its cost is at most the sum of the costs of the factorwise quotients:
--
--   $$
--   \kappa\bigl(AB^{-1}\bigr)\le\sum_{k=1}^{n}\kappa\bigl(a(j_k)\,b(j_k)^{-1}\bigr).
--   $$
--
--   This controls how far apart two products are, factor by factor: when corresponding factors are close in $L$, so are the products. It is the basic estimate behind averaging words over a finite group, where an average is a product over all group elements.
--
--   **Formalization Note** The cost is the structure `NormalCost L` with fields `cost`, `nonneg`, `one`, `inv`, `conj` and `mul`; for the empty list both products are $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/NormalCost.lean#L74-L91

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

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.NormalCost
universe uGroup uAction uPoint uAlpha
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
open scoped BigOperators commutatorElement
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X]
variable {L : Subgroup G} [L.Normal] (c : NormalCost L)

theorem OAI.EuclideanRamsey.NormalCost.product_difference {α : Type uAlpha} (l : List α) (a b : α → G)
    (h : ∀ j∈l,a j*(b j)⁻¹∈L) :
    (l.map a).prod*((l.map b).prod)⁻¹∈L ∧
    c.cost ((l.map a).prod*((l.map b).prod)⁻¹) ≤
      (l.map (fun j => c.cost (a j*(b j)⁻¹))).sum := by sorry
