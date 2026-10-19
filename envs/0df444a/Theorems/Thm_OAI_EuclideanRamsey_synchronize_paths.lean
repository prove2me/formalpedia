-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_synchronize_paths
-- name    : OAI.EuclideanRamsey.synchronize_paths
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:32:04.844016+00:00
-- url     : https://prove2.me/theorems/5f6a74bc-e975-4434-b8af-41cacd24bc08
-- title:
--   One word family with paths of every weight $1/t$, $1\le t\le n$
-- statement:
--   Let $E=\mathbb{R}^{(\mathbb{N})}$ be the real inner-product space of finitely supported sequences with $\langle x,y\rangle=\sum_n x_ny_n$, and let $F$ be the free group on the set $E$, with generator $[z]$ for $z\in E$. Fix an index set $\iota$ and points $a=(a_i)_{i\in\iota}$ in $E$. A family $w=(w_i)_{i\in\iota}$ in $F$ *has a path of weight $\lambda$* if this follows from the rules: every constant family $(g)_{i\in\iota}$ has weight $0$; a family $([b_i])_{i\in\iota}$ with $b_i\in E$ has weight $u$ whenever $u\ge0$ and $\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2$ for all $i,j$ (a copy of $a$ scaled by $\sqrt u$); and the pointwise product $(w_iw'_i)_i$ of families of weights $\lambda$ and $\mu$ has weight $\lambda+\mu$. The same family may have paths of several different weights.
--
--   **Theorem.** Let $n\ge1$ be an integer and let $w$ be a family in $F$ that has a path of weight $\lambda$ and a path of weight $\mu$, where
--
--   $$
--   \lambda>0\qquad\text{and}\qquad\frac{\mu}{\lambda}<\frac1n .
--   $$
--
--   Then there is a single family $W$ in $F$ that has a path of weight $1/t$ for every integer $t$ with $1\le t\le n$.
--
--   A family carrying the weights $1,\tfrac12,\dots,\tfrac1n$ simultaneously is exactly what the Euclidean Ramsey argument needs: once a combinatorial line with $t$ active coordinates has been selected by the Hales–Jewett theorem, $t$ copies of a path of weight $1/t$ add up to total weight exactly $1$, which corresponds to a congruent copy of $a$.
--
--   **Formalization Note** $E$ is `FiniteEuclidean`, $F$ is `LetterGroup` (`FreeGroup FiniteEuclidean`), and "has a path of weight $\lambda$" is the inductive predicate `Path a w λ`; the weights $1/t$ are real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/PathSynchronization.lean#L101-L127

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

open OAI OAI.EuclideanRamsey
universe uIndex uAlpha
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
open scoped BigOperators
variable {ι : Type uIndex} {a : ι → FiniteEuclidean}

theorem OAI.EuclideanRamsey.synchronize_paths (n : ℕ) (hn : 1 ≤ n) {w : ι → LetterGroup} {lmb μ : ℝ}
    (hp : Path a w lmb) (hm : Path a w μ) (hlmb : 0 < lmb)
    (hratio : μ/lmb < 1/(n:ℝ)) :
    ∃ W,∀ t : ℕ,1 ≤ t → t ≤ n → Path a W (1/(t:ℝ)) := by sorry
