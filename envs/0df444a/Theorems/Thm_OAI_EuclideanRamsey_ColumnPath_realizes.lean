-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_ColumnPath_realizes
-- name    : OAI.EuclideanRamsey.ColumnPath.realizes
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:26:20.346016+00:00
-- url     : https://prove2.me/theorems/4a45ee88-1e34-423f-9a79-e32309999b59
-- title:
--   Realizing a column path of weight $u$ yields a string family of weight $u$
-- statement:
--   Let $E=\mathbb{R}^{(\mathbb{N})}$ be the real inner-product space of finitely supported sequences $x=(x_n)_{n\in\mathbb{N}}$ with $\langle x,y\rangle=\sum_n x_ny_n$, and let $\mathcal S$ be the free monoid on the set $E$: its elements are finite strings $(z_1,\dots,z_m)$ of points of $E$, multiplied by concatenation, and $(z)$ denotes a one-letter string. For two strings $\sigma=(z_1,\dots,z_m)$ and $\tau=(z'_1,\dots,z'_m)$ of equal length put $\mathcal E(\sigma,\tau)=\sum_{k=1}^m\|z_k-z'_k\|^2$.
--
--   Fix an index set $\iota$ and a configuration $a=(a_i)_{i\in\iota}$ in $E$. A *column* over $\mathcal S$ is either a common column $\mathrm{com}(U)$, with $U$ an ultrafilter on $\mathcal S$, which is realized by every constant tuple in $\mathcal S^{\iota}$, or a principal column $\mathrm{pr}(x)$ with $x\in\mathcal S^{\iota}$, which is realized only by $x$. A list of columns is a *column path of weight $u$* for $a$ if this follows from the rules:
--
--   1. the empty list has weight $0$;
--   2. a single common column $\mathrm{com}(U)$ has weight $0$;
--   3. if $u\ge 0$ and $b=(b_i)_{i\in\iota}$ in $E$ satisfies $\|b_i-b_j\|^2=u\,\|a_i-a_j\|^2$ for all $i,j$, the single principal column $\mathrm{pr}\bigl(i\mapsto(b_i)\bigr)$ has weight $u$;
--   4. if $p$ is a column path of weight $u$ and $q$ one of weight $v$, the concatenation $p\,q$ has weight $u+v$.
--
--   **Theorem.** Let $q_1,\dots,q_n$ be a column path of weight $u$ for $a$, and let $x^{(1)},\dots,x^{(n)}\in\mathcal S^{\iota}$ be tuples with $x^{(k)}$ realizing $q_k$ for every $k$. Put $X_i=x^{(1)}_i x^{(2)}_i\cdots x^{(n)}_i\in\mathcal S$. Then all strings $X_i$ have the same length and
--
--   $$
--   \mathcal E(X_i,X_j)=u\,\|a_i-a_j\|^2\qquad\text{for all } i,j\in\iota .
--   $$
--
--   In other words, realizing a column path always produces a *string family of weight $u$*. When $u=1$ and the strings are turned into points by placing their letters in mutually orthogonal blocks of coordinates, $\mathcal E$ becomes the squared distance, so the realized strings give a congruent copy of $a$; this is how monochromatic congruent copies are extracted in the Euclidean Ramsey argument.
--
--   **Formalization Note** $E$ is `FiniteEuclidean` (finitely supported functions $\mathbb{N}\to\mathbb{R}$), $\mathcal S$ is `Strings`, the free monoid on `FiniteEuclidean`, column paths are the inductive predicate `ColumnPath a qs u`, and the conclusion is `StringFamily a u X`. The energy `stringEnergy` is defined recursively and stops at the end of the shorter string; since equal lengths are part of the conclusion, it is the full sum above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/UltrafilterStrings.lean#L124-L157

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

open OAI OAI.EuclideanRamsey
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
open Filter
attribute [local instance] Ultrafilter.mul Ultrafilter.semigroup
variable {ι : Type uIndex}

theorem OAI.EuclideanRamsey.ColumnPath.realizes {a : ι → FiniteEuclidean} {qs u} (h : ColumnPath a qs u)
    (xs : List (ι → Strings)) (hx : List.Forall₂ UltraColumn.Realizes qs xs) :
    StringFamily a u (fun i => (xs.map (fun x => x i)).prod) := by sorry
