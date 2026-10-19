-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_evolve_finite
-- name    : OAI.EuclideanRamsey.evolve_finite
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:43:20.152682+00:00
-- url     : https://prove2.me/theorems/d596706d-ed0d-4f9f-a1e6-48854002e0e2
-- title:
--   Pointwise improvements of an evolution combine over a finite set
-- statement:
--   Let $G$ be a group and let a finite group $H$ act on a set $X$. Fix an enumeration $g_1,\dots,g_{|H|}$ of $H$ and, for $v:X\to G$, let $\mathrm{Av}_v(x)=v(g_1\cdot x)\,v(g_2\cdot x)\cdots v(g_{|H|}\cdot x)$ be the orbit average. Pairs $(v,n)$, consisting of a map $v:X\to G$ and a natural number $n$ (a length counter), can be transformed by two operations:
--
--   - *normalization*: $(v,n)\mapsto\bigl(x\mapsto v(x)\,c,\ n\bigr)$ for a constant $c\in G$;
--   - *averaging*: $(v,n)\mapsto\bigl(\mathrm{Av}_v,\ |H|\,n\bigr)$.
--
--   Write $(w,m)\leadsto(v,n)$, and call $(v,n)$ an *evolution* of $(w,m)$, if $(v,n)$ is obtained from $(w,m)$ by finitely many such operations (possibly none).
--
--   **Theorem.** Assume $X$ is finite. Let $w:X\to G$, $m\in\mathbb{N}$, and let $\mathrm{Good}(x,v,n)$ be any property of a point $x\in X$ and a pair $(v,n)$. Assume:
--
--   1. (*preservation*) for all pairs with $(v,n)\leadsto(u,k)$ and all $x\in X$, $\mathrm{Good}(x,v,n)$ implies $\mathrm{Good}(x,u,k)$;
--   2. (*improvement*) for every evolution $(v,n)$ of $(w,m)$ and every $x\in X$ there is a pair $(u,k)$ with $(v,n)\leadsto(u,k)$ and $\mathrm{Good}(x,u,k)$.
--
--   Then a single evolution is good everywhere:
--
--   $$
--   \exists\,(v,n):\qquad (w,m)\leadsto(v,n)\quad\text{and}\quad \mathrm{Good}(x,v,n)\ \text{ for all } x\in X .
--   $$
--
--   This lets one establish a property point by point (for instance orbit by orbit): it suffices to be able to improve any evolved pair at one point at a time, provided that further evolution never destroys what has already been achieved.
--
--   **Formalization Note** Evolutions are the inductive predicate `Evolution w m v n` with constructors `refl`, `normalize` (right multiplication by a constant) and `average`; the enumeration of $H$ is the fixed list `groupList H`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/OrbitAveraging.lean#L186-L204

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
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_NormalCost
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_OrbitAveraging

open OAI OAI.EuclideanRamsey
universe uGroup uAction uPoint
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
open scoped BigOperators
variable {G : Type uGroup} {H : Type uAction} {X : Type uPoint} [Group G] [Group H] [MulAction H X] [Fintype H]

theorem OAI.EuclideanRamsey.evolve_finite [Fintype X] (w : X → G) (m : ℕ)
    (Good : X → (X → G) → ℕ → Prop)
    (preserve : ∀ {v n u k},Evolution (H:=H) v n u k → ∀ x,Good x v n → Good x u k)
    (improve : ∀ {v n},Evolution (H:=H) w m v n → ∀ x,
      ∃ u k,Evolution (H:=H) v n u k ∧ Good x u k) :
    ∃ v n,Evolution (H:=H) w m v n ∧ ∀ x,Good x v n := by sorry
