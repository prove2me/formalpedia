-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_exists_group_corner
-- name    : OAI.EuclideanRamsey.exists_group_corner
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:33:34.86899+00:00
-- url     : https://prove2.me/theorems/56012e3e-4932-47bb-9e26-4aeeb38fac1b
-- title:
--   A compact right topological semigroup has an idempotent whose corner is a group
-- statement:
--   Let $S$ be a nonempty semigroup carrying a compact Hausdorff topology in which every right translation $x\mapsto xy$ $(y\in S)$ is continuous, i.e. a compact right topological semigroup. Then $S$ contains an idempotent $p$ such that every element $y$ of the corner $pSp=\{y\in S:\ py=y=yp\}$ has a left inverse relative to $p$ inside the corner:
--
--   $$
--   \exists\,p\in S:\quad p^2=p\quad\text{and}\quad\forall y\in S\ \Bigl(py=y=yp\ \Longrightarrow\ \exists\,v\in S:\ pv=v=vp,\ \ vy=p\Bigr).
--   $$
--
--   Consequently the corner $pSp$, with the multiplication of $S$ and identity $p$, is a group. The intended application is the semigroup of ultrafilters on a free monoid of strings, where right translations are continuous for the ultrafilter product: the free group on the letters then maps homomorphically into this group, which is how free-group words are pushed into ultrafilters in the Euclidean Ramsey argument.
--
--   **Formalization Note** The hypotheses are the type classes `Nonempty S`, `Semigroup S`, `CompactSpace S`, `T2Space S` and the assumption that `fun x => x * y` is continuous for every `y`. The group structure on the corner is built from this statement separately (`Corner.group`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CornerGroup.lean#L30-L73

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

open OAI OAI.EuclideanRamsey
universe uSemigroup
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

theorem OAI.EuclideanRamsey.exists_group_corner {S : Type uSemigroup} [Nonempty S] [Semigroup S]
    [TopologicalSpace S] [CompactSpace S] [T2Space S]
    (hc : ∀ y : S, Continuous (· * y)) :
    ∃ p : S, p*p=p ∧ ∀ y : S, p*y=y → y*p=y →
      ∃ v : S, p*v=v ∧ v*p=v ∧ v*y=p := by sorry
