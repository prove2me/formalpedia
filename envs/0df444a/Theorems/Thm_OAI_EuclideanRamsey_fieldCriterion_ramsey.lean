-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_fieldCriterion_ramsey
-- name    : OAI.EuclideanRamsey.fieldCriterion_ramsey
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:37:16.245899+00:00
-- url     : https://prove2.me/theorems/bdc2cac2-2832-4ecd-ac1f-f57ee4e8e711
-- title:
--   The field tensor criterion implies the Euclidean Ramsey property
-- statement:
--   Let $s\ge2$ and $d\ge1$ be integers and let $a_0,\dots,a_{s-1}$ be pairwise distinct points of the Euclidean space $\mathbb{R}^d$, where $a_i$ has coordinates $a_{i1},\dots,a_{id}$. Let $K\subseteq\mathbb{R}$ be the subfield generated over $\mathbb{Q}$ by all coordinates $a_{ij}$, let $\hat a_i$ be the augmented coordinate vector of $a_i$, indexed by $\{\ast,1,\dots,d\}$ with $\hat a_i(\ast)=1$ and $\hat a_i(j)=a_{ij}$, and let $m:K\otimes_{\mathbb{Q}}K\to K$, $u\otimes v\mapsto uv$, be the multiplication map. Assume that $a$ satisfies the *field criterion*: there is a matrix $(P_{\alpha\beta})_{\alpha,\beta\in\{\ast,1,\dots,d\}}$ with entries in $K\otimes_{\mathbb{Q}}K$ such that
--
--   $$
--   \sum_{\alpha,\beta\in\{\ast,1,\dots,d\}}\bigl(\hat a_i(\alpha)\otimes1\bigr)P_{\alpha\beta}\bigl(1\otimes\hat a_i(\beta)\bigr)=0\quad(0\le i\le s-1),\qquad m(P_{\alpha\beta})=\delta_{\alpha\beta}\quad(1\le\alpha,\beta\le d).
--   $$
--
--   Then $a$ is *Ramsey*: for every number of colours $r\ge2$ there is a dimension $D\ge1$ such that for every colouring $c:\mathbb{R}^D\to\{0,\dots,r-1\}$ there are points $b_0,\dots,b_{s-1}\in\mathbb{R}^D$ and a colour $k$ with
--
--   $$
--   \|b_i-b_j\|=\|a_i-a_j\|\quad\text{for all }0\le i,j\le s-1,\qquad c(b_0)=c(b_1)=\dots=c(b_{s-1})=k .
--   $$
--
--   Thus a purely algebraic certificate over the coordinate field forces monochromatic congruent copies of $a$ in every finite colouring of a sufficiently high-dimensional Euclidean space. No assumption on the affine span of the points is made. This is the step that turns the algebraic certificate into the Ramsey property when showing that subsets of finite transitive configurations are Ramsey.
--
--   **Formalization Note** Points of $\mathbb{R}^d$ are elements of `Space d = EuclideanSpace ℝ (Fin d)` and the configuration is an injective map `a : Fin s → Space d`. The hypothesis is `FieldCriterion a` (built from `coordinateField a`, `augmented a i` and `multiply a`, with augmented index set `Option (Fin d)`). The conclusion `Ramsey a` asks, for each `r` with `2 ≤ r`, for some `D` with `1 ≤ D` such that every `c : Space D → Fin r` admits `b : Fin s → Space D` with `Congruent a b` (all pairwise distances equal) and `c` constant on the points of `b`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Main.lean#L28-L67

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

theorem OAI.EuclideanRamsey.fieldCriterion_ramsey {s d : ℕ} (a : Fin s → Space d)
    (hs : 2 ≤ s) (hd : 1 ≤ d) (ha : Function.Injective a)
    (h : FieldCriterion a) : Ramsey a := by sorry
