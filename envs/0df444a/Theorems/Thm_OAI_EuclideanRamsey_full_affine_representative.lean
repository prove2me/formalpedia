-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_full_affine_representative
-- name    : OAI.EuclideanRamsey.full_affine_representative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:41:14.506326+00:00
-- url     : https://prove2.me/theorems/471c9d11-3625-4709-8fe1-3497d39c86ae
-- title:
--   Distinct points have a congruent copy that affinely spans some $\mathbb{R}^d$ with $d\ge1$
-- statement:
--   Let $s\ge2$ and $D\ge0$ be integers and let $a_0,\dots,a_{s-1}$ be pairwise distinct points of the Euclidean space $\mathbb{R}^D$. Then there exist an integer $d\ge1$ and pairwise distinct points $b_0,\dots,b_{s-1}\in\mathbb{R}^d$ such that
--
--   $$
--   \|b_i-b_j\|=\|a_i-a_j\|\quad\text{for all }0\le i,j\le s-1,\qquad\operatorname{aff}\{b_0,\dots,b_{s-1}\}=\mathbb{R}^d,
--   $$
--
--   where $\operatorname{aff}$ denotes the affine span (the smallest affine subspace containing the points).
--
--   In words, every configuration of at least two distinct points is congruent to a configuration that is full-dimensional in its ambient Euclidean space of positive dimension. Since properties defined only through pairwise distances, such as being Ramsey, are invariant under congruence, this reduces such questions to affinely spanning configurations, which is the setting in which congruent copies are images under isometric affine maps and in which algebraic criteria for the Ramsey property are formulated.
--
--   **Formalization Note** The statement uses `Space d = EuclideanSpace ℝ (Fin d)`, injectivity of `a : Fin s → Space D` and of `b : Fin s → Space d`, the relation `Congruent a b` (meaning `dist (b i) (b j) = dist (a i) (a j)` for all `i j`), and `affineSpan ℝ (Set.range b) = ⊤`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Main.lean#L78-L123

import Mathlib
import Definitions.Def_EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorPresentation__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SignedRows__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_FiniteEuclidean__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DerivedFractions__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathWords__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_UltrafilterStrings__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_PathSynchronization__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CornerGroup__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_ColoringCompactness__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging__EuclideanRamseyTransitive
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CorrectionPaths__EuclideanRamseyTransitive

open OAI OAI.EuclideanRamsey
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

theorem OAI.EuclideanRamsey.full_affine_representative {s D : ℕ} (a : Fin s → Space D)
    (hs : 2 ≤ s) (ha : Function.Injective a) :
    ∃ d : ℕ,1 ≤ d ∧ ∃ b : Fin s → Space d,Function.Injective b ∧
      Congruent a b ∧ affineSpan ℝ (Set.range b)=⊤ := by sorry
