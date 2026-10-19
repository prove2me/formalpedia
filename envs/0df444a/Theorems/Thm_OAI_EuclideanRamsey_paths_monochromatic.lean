-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_paths_monochromatic
-- name    : OAI.EuclideanRamsey.paths_monochromatic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:34:26.484679+00:00
-- url     : https://prove2.me/theorems/74952675-c6b5-4d13-a062-5e22eacd6c9b
-- title:
--   Word families with arbitrarily small path-weight ratio give monochromatic congruent copies
-- statement:
--   Let $E=\mathbb{R}^{(\mathbb{N})}$ be the real inner-product space of finitely supported sequences with $\langle x,y\rangle=\sum_n x_ny_n$ and norm $\|\cdot\|$; it contains every $\mathbb{R}^d$ isometrically. Let $F$ be the free group on the set $E$, with generator $[z]$ for $z\in E$. For a configuration $a=(a_0,\dots,a_{s-1})$ of $s$ points in $E$, say that a family $w=(w_0,\dots,w_{s-1})$ in $F$ *has a path of weight $\lambda$* if this follows from the rules: a constant family $(g,\dots,g)$ has weight $0$; a family $([b_0],\dots,[b_{s-1}])$ with $b_i\in E$ has weight $u$ whenever $u\ge0$ and $\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2$ for all $i,j$; and the pointwise product of families of weights $\lambda$ and $\mu$ has weight $\lambda+\mu$.
--
--   **Theorem.** Suppose that for every integer $n\ge1$ there are a family $w$ in $F$ and reals $\lambda,\mu$ such that $w$ has a path of weight $\lambda$ and a path of weight $\mu$, with $\lambda>0$ and $\mu/\lambda<1/n$. Then for every finite set $K$ of colours and every colouring $c:E\to K$ there are points $b_0,\dots,b_{s-1}\in E$ and a colour $k\in K$ with
--
--   $$
--   \|b_i-b_j\|=\|a_i-a_j\|\quad\text{for all } i,j\qquad\text{and}\qquad c(b_i)=k\quad\text{for all } i .
--   $$
--
--   So a configuration whose word families admit paths with arbitrarily small weight ratio is Ramsey in the infinite-dimensional space $E$: every finite colouring of $E$ contains a monochromatic congruent copy of it. Combined with a compactness argument that passes from $E$ to a single finite dimension, this is used to prove that configurations satisfying the field criterion of the Euclidean Ramsey classification are Ramsey.
--
--   **Formalization Note** $E$ is `FiniteEuclidean`, $F$ is `LetterGroup` (`FreeGroup FiniteEuclidean`), the path predicate is `Path a w λ`, and the colour set is an arbitrary type with a `Finite` instance. The family $w$ and the weights may depend on $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/ColoringCompactness.lean#L59-L121

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
open Filter
open scoped BigOperators
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup

theorem OAI.EuclideanRamsey.paths_monochromatic {s : ℕ} (a : Fin s → FiniteEuclidean)
    (hpaths : ∀ n : ℕ,1 ≤ n → ∃ w lmb μ,Path a w lmb ∧ Path a w μ ∧
      0 < lmb ∧ μ/lmb < 1/(n:ℝ))
    {κ : Type uColor} [Finite κ] (c : FiniteEuclidean → κ) :
    ∃ b : Fin s → FiniteEuclidean,(∀ i j,‖b i-b j‖=‖a i-a j‖) ∧
      ∃ k : κ,∀ i,c (b i)=k := by sorry
