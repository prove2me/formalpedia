-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_finite_coloring_compactness
-- name    : OAI.EuclideanRamsey.finite_coloring_compactness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:36:59.478071+00:00
-- url     : https://prove2.me/theorems/bebd4005-f22a-435d-aed9-cb864d87b18d
-- title:
--   Compactness: monochromatic congruent copies in $\mathbb{R}^{(\mathbb{N})}$ already occur in some $\mathbb{R}^D$
-- statement:
--   Let $E=\mathbb{R}^{(\mathbb{N})}$ be the real inner-product space of finitely supported sequences with $\langle x,y\rangle=\sum_n x_ny_n$; it contains each Euclidean space $\mathbb{R}^D$ isometrically as the sequences supported on the first $D$ coordinates. Let $a=(a_0,\dots,a_{s-1})$ be points of $E$ and let $r\in\mathbb{N}$ be a number of colours.
--
--   **Theorem.** Suppose every colouring $c:E\to\{0,\dots,r-1\}$ admits a monochromatic congruent copy of $a$, i.e. points $b_0,\dots,b_{s-1}\in E$ and a colour $k$ with $\|b_i-b_j\|=\|a_i-a_j\|$ for all $i,j$ and $c(b_i)=k$ for all $i$. Then there is a dimension $D\ge1$ such that every colouring of $\mathbb{R}^D$ already does so:
--
--   $$
--   \forall\,c:\mathbb{R}^D\to\{0,\dots,r-1\}\ \ \exists\,b_0,\dots,b_{s-1}\in\mathbb{R}^D,\ \exists\,k:\quad \|b_i-b_j\|=\|a_i-a_j\|\ \ \forall i,j,\qquad c(b_i)=k\ \ \forall i .
--   $$
--
--   This compactness principle reduces the Euclidean Ramsey property, which asks for a finite dimension depending on the number of colours, to the corresponding statement in the single infinite-dimensional space $E$. In the classification of Ramsey configurations it is combined with the construction of monochromatic congruent copies in $E$.
--
--   **Formalization Note** $E$ is `FiniteEuclidean` and $\mathbb{R}^D$ is `EuclideanSpace ℝ (Fin D)`; the distances $\|b_i-b_j\|$ in the conclusion are computed in $\mathbb{R}^D$ and $\|a_i-a_j\|$ in $E$. The numbers $s$ and $r$ are arbitrary natural numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean#L150-L185

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

open OAI OAI.EuclideanRamsey
universe uModule uColor
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

theorem OAI.EuclideanRamsey.finite_coloring_compactness {s : ℕ} (a : Fin s → FiniteEuclidean) (r : ℕ)
    (h : ∀ c : FiniteEuclidean → Fin r,∃ b : Fin s → FiniteEuclidean,
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k) :
    ∃ D : ℕ,1≤D ∧ ∀ c : EuclideanSpace ℝ (Fin D) → Fin r,
      ∃ b : Fin s → EuclideanSpace ℝ (Fin D),
      (∀ i j,‖b i-b j‖=‖a i-a j‖) ∧ ∃ k : Fin r,∀ i,c (b i)=k := by sorry
