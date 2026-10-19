-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_augmentation_kernel_le
-- name    : OAI.EuclideanRamsey.augmentation_kernel_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:22:41.465232+00:00
-- url     : https://prove2.me/theorems/41adaada-3985-4578-9488-126cf50c19d0
-- title:
--   A normal subgroup of a free group that identifies all generators contains the augmentation kernel
-- statement:
--   Let $X$ be a set with a chosen element $x_0\in X$, let $F(X)$ be the free group on $X$, and let $\varepsilon:F(X)\to\mathbb Z$ be the augmentation homomorphism sending every generator $x\in X$ to $1$ (so $\varepsilon(w)$ is the exponent sum of the word $w$). Let $K=\ker\varepsilon$ be the subgroup of words with exponent sum $0$.
--
--   **Theorem.** Let $Q$ be a normal subgroup of $F(X)$ such that all generators have the same image in the quotient group, i.e. $xQ=yQ$ in $F(X)/Q$ for all $x,y\in X$. Then
--   $$K\subseteq Q .$$
--
--   In other words, $K$ is the smallest normal subgroup modulo which all generators become equal. The lemma reduces membership in $K$ to a "connectivity" statement: to show $K\subseteq Q$ it suffices to show that any two generators are congruent modulo $Q$, for example by joining them through a chain of elementary steps.
--
--   **Formalization Note** $\varepsilon$ is `freeAugmentation X : FreeGroup X →* Multiplicative ℤ` and $K$ is `AugKernel X`; the hypothesis is stated with the quotient map `QuotientGroup.mk' Q` applied to `FreeGroup.of x`. The base point $x_0$ is only used to name a common image.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/DerivedFractions.lean#L190-L208

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

open OAI OAI.EuclideanRamsey
universe uGroup uIndex uColor uPoint
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
variable {X : Type uPoint} {G : Type uGroup} [Group G]

theorem OAI.EuclideanRamsey.augmentation_kernel_le (x₀ : X) (Q : Subgroup (FreeGroup X)) [Q.Normal]
    (h : ∀ x y,(QuotientGroup.mk' Q) (FreeGroup.of x)=(QuotientGroup.mk' Q) (FreeGroup.of y)) :
    AugKernel X≤Q := by sorry
