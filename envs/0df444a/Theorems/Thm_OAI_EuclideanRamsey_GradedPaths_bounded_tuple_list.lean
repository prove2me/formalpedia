-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_GradedPaths_bounded_tuple_list
-- name    : OAI.EuclideanRamsey.GradedPaths.bounded_tuple_list
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:21:32.633188+00:00
-- url     : https://prove2.me/theorems/2fdc26a0-096b-40eb-b047-7dcd77b2ac4c
-- title:
--   Costs of single-coordinate fractions add along a product of such fractions
-- statement:
--   Let $G$ be a group and $\iota$ an index set, and regard $G^\iota$ as a group under coordinatewise multiplication. For $i\in\iota$ and $g\in G$ let $e_i(g)\in G^\iota$ be the tuple with $g$ in coordinate $i$ and $1$ elsewhere. A *graded path system* $\mathcal P$ on $(\iota,G)$ is a relation "$u$ is realized with cost $m$" between tuples $u\in G^\iota$ and natural numbers $m$ such that every constant tuple $(g,g,\dots)$ is realized with cost $0$, and if $u$ is realized with cost $m$ and $u'$ with cost $m'$ then $uu'$ is realized with cost $m+m'$. A tuple $z$ is a *bounded fraction of cost $c$* if $z=uv^{-1}$ where $u$ is realized with cost $m$, $v$ with cost $m'$, and $m+m'\le c$.
--
--   **Theorem.** Let $(i_1,\dots,i_r)$ be a finite list of indices (repetitions allowed), let $z:\iota\to G$ and $c:\iota\to\mathbb N$. If for every index $i$ occurring in the list the tuple $e_i(z_i)$ is a bounded fraction of cost $c_i$, then the ordered product
--   $$e_{i_1}(z_{i_1})\,e_{i_2}(z_{i_2})\cdots e_{i_r}(z_{i_r})\ \text{ is a bounded fraction of cost }\ c_{i_1}+c_{i_2}+\dots+c_{i_r}.$$
--   For the empty list this says that the identity tuple is a bounded fraction of cost $0$.
--
--   The lemma makes the cost of a single-coordinate correction additive: a tuple assembled coordinate by coordinate from single-coordinate fractions costs at most the sum of their individual costs. It is used to bound the total cost of correcting all coordinates of a tuple at once.
--
--   **Formalization Note** The graded path system is a structure `GradedPaths ι G` with predicate `Holds`; bounded fractions are `P.BoundedFraction z c`, $e_i(g)$ is `Pi.mulSingle i g`, and the list product and cost sum are `(l.map (fun i => Pi.mulSingle i (z i))).prod` and `(l.map c).sum`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathFractions.lean#L222-L241

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

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.GradedPaths
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
open scoped BigOperators
variable {G : Type uGroup} {ι : Type uIndex} [Group G] [DecidableEq ι]
variable (P : GradedPaths ι G)

theorem OAI.EuclideanRamsey.GradedPaths.bounded_tuple_list (l : List ι) (z : ι → G) (c : ι → ℕ)
    (h : ∀ i∈l,P.BoundedFraction (Pi.mulSingle i (z i)) (c i)) :
    P.BoundedFraction ((l.map (fun i => Pi.mulSingle i (z i))).prod) ((l.map c).sum) := by sorry
