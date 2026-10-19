-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_RightFraction_mul_pair
-- name    : OAI.EuclideanRamsey.RightFraction.mul_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:20:59.649018+00:00
-- url     : https://prove2.me/theorems/f2dd81ca-9e6c-4956-a372-60ce470b44b0
-- title:
--   Right fractions of a pair-inverse monoid are closed under multiplication by fractions supported on two coordinates
-- statement:
--   Let $G$ be a group and $\iota$ an index set, and regard $G^\iota$ (all functions $\iota\to G$) as a group under coordinatewise multiplication. Let $M\subseteq G^\iota$ be a submonoid. A tuple $z\in G^\iota$ is a *right fraction* of $M$ if $z=uv^{-1}$ for some $u,v\in M$. The monoid $M$ has the *pair-inverse property* if for all distinct $i,j\in\iota$ and every $v\in M$ there is $b\in M$ with $v_i\,b_i=1$ and $v_j\,b_j=1$.
--
--   **Theorem.** Suppose $M$ has the pair-inverse property. Let $z$ and $t$ be right fractions of $M$, let $i\ne j$ be two indices, and assume $t_l=1$ for every index $l\notin\{i,j\}$. Then
--   $$z\,t\ \text{ is a right fraction of } M .$$
--
--   Right fractions are evidently closed under inversion, but not obviously under products. This lemma gives closure under multiplication by fractions supported on two coordinates. Applied three times it shows that the commutator of two fractions supported on $\{i,j\}$ and $\{i,k\}$ is a fraction supported on the single coordinate $i$, which is the engine of the derived-series argument for single-coordinate fractions.
--
--   **Formalization Note** Right fractions and the pair-inverse property are `RightFraction M z` and `PairInverse M`; $\iota$ carries decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean#L97-L117

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

open OAI OAI.EuclideanRamsey
universe uGroup uIndex
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
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]

theorem OAI.EuclideanRamsey.RightFraction.mul_pair {M : Submonoid (ι → G)} (hM : PairInverse M)
    {z t : ι → G} (hz : RightFraction M z) (ht : RightFraction M t)
    (i j : ι) (hij : i≠j) (hs : ∀ l,l≠i → l≠j → t l=1) :
    RightFraction M (z*t) := by sorry
