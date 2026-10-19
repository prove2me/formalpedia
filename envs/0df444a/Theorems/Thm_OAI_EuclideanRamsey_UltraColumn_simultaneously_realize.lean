-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_UltraColumn_simultaneously_realize
-- name    : OAI.EuclideanRamsey.UltraColumn.simultaneously_realize
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:25:47.897908+00:00
-- url     : https://prove2.me/theorems/0bbd527b-6894-4391-8986-a3765301bb13
-- title:
--   Simultaneous realization of coordinatewise products of ultrafilter columns
-- statement:
--   Let $M$ be a monoid and let $\beta M$ be the set of ultrafilters on $M$, with the product
--   $$
--   A\in U\cdot V\iff\bigl\{x\in M:\ \{y\in M:\ xy\in A\}\in V\bigr\}\in U .
--   $$
--   This makes $\beta M$ a monoid whose identity is $\delta_1$, where $\delta_x$ denotes the principal ultrafilter at $x$.
--
--   Let $\iota$ be a **finite** index set. A *column* (over $M$, indexed by $\iota$) is either a common column $\mathrm{com}(U)$ with $U\in\beta M$, or a principal column $\mathrm{pr}(x)$ with $x\in M^{\iota}$. Its value at a coordinate $i\in\iota$ is $\mathrm{com}(U)(i)=U$, respectively $\mathrm{pr}(x)(i)=\delta_{x_i}$. A tuple $y\in M^{\iota}$ *realizes* $\mathrm{com}(U)$ if $y$ is constant ($y_i=y_j$ for all $i,j$), and it realizes $\mathrm{pr}(x)$ if $y=x$.
--
--   **Theorem.** Let $q_1,\dots,q_n$ be a finite list of columns and let $B_i\subseteq M$ $(i\in\iota)$ be sets with $B_i\in q_1(i)\cdot q_2(i)\cdots q_n(i)$ for every $i$ (the empty product being $\delta_1$). Then there are tuples $x^{(1)},\dots,x^{(n)}\in M^{\iota}$ such that $x^{(k)}$ realizes $q_k$ for each $k$ and
--
--   $$
--   x^{(1)}_i\,x^{(2)}_i\cdots x^{(n)}_i\in B_i\qquad\text{for every } i\in\iota .
--   $$
--
--   A common column has to be realized by one and the same element of $M$ in all coordinates at once, while principal columns are prescribed. In the Euclidean Ramsey argument this turns the statement "a colour class belongs to the ultrafilter product in every coordinate" into actual strings whose coordinatewise products lie in that colour class, with all shared (common) parts identical across coordinates.
--
--   **Formalization Note** The monoid structure on $\beta M$ is `ultrafilterMonoid`, built on Mathlib's ultrafilter multiplication `Ultrafilter.mul` with unit `pure 1`; the products are list products of `q.value i` in list order. The realizing tuples are returned as a list related to the column list by `List.Forall₂ Realizes`, which in particular forces it to have the same length $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean#L85-L109

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

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.UltraColumn
universe uModule uIndex uAlpha
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
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex} {M : Type uModule}

theorem OAI.EuclideanRamsey.UltraColumn.simultaneously_realize [Finite ι] [Monoid M] (qs : List (UltraColumn ι M))
    (B : ι → Set M)
    (h : letI := ultrafilterMonoid (M:=M)
      ∀ i,B i ∈ ((qs.map (fun q => q.value i)).prod : Ultrafilter M)) :
    ∃ xs : List (ι → M), List.Forall₂ Realizes qs xs ∧
      ∀ i, (xs.map (fun x => x i)).prod ∈ B i := by sorry
