-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CI_normalized_count_constant
-- name    : OAI.PermanentBorder.CI.normalized_count_constant
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:54:50.128337+00:00
-- url     : https://prove2.me/theorems/17b7fed3-640a-4d46-8762-487eb3637cc8
-- title:
--   Root counts are constant along a preconnected family of good homogeneous systems
-- statement:
--   Let $\iota$ be a finite set and $\iota_\ast=\{\ast\}\sqcup\iota$; we work with complex polynomials in the $|\iota|+1$ variables $X_j$, $j\in\iota_\ast$. For a system $H=(H_i)_{i\in\iota}$ of such polynomials and a coefficient vector $l\in\mathbb{C}^{\iota_\ast}$ write $\ell(y)=\sum_{j\in\iota_\ast}l_jy_j$ and
--   $$
--   \mathrm{Roots}(H,l)=\{y\in\mathbb{C}^{\iota_\ast} : H_i(y)=0\ \text{for all } i\in\iota,\ \ell(y)=1\}.
--   $$
--   The pair $(H,l)$ is called *good* if every common zero $y\ne0$ of the $H_i$ satisfies $\ell(y)\ne0$ and $\det J_{H,l}(y)\ne0$, where $J_{H,l}(y)$ is the $\iota_\ast\times\iota_\ast$ matrix whose row $\ast$ is $(l_j)_{j\in\iota_\ast}$ and whose row $i\in\iota$ is the gradient $(\partial_jH_i(y))_{j\in\iota_\ast}$.
--
--   Now let $H_t=(H_{t,i})_{i\in\iota}$ and $l_t\in\mathbb{C}^{\iota_\ast}$ be families indexed by $t\in\mathbb{C}$, let $e:\iota\to\mathbb{N}$ and let $S\subseteq\mathbb{C}$. Assume:
--   1. $H_{t,i}$ is homogeneous of degree $e_i$ for every $t\in\mathbb{C}$ and every $i\in\iota$;
--   2. the normalized system $N(t,y)=\big(\ell_t(y)-1,\ (H_{t,i}(y))_{i\in\iota}\big)$, viewed as a map $\mathbb{C}\times\mathbb{C}^{\iota_\ast}\to\mathbb{C}^{\iota_\ast}$, is continuously complex-differentiable ($C^1$) on all of $\mathbb{C}\times\mathbb{C}^{\iota_\ast}$;
--   3. $S$ is preconnected and $(H_t,l_t)$ is good for every $t\in S$.
--
--   Then for all $a,b\in S$
--   $$
--   \#\,\mathrm{Roots}(H_a,l_a)=\#\,\mathrm{Roots}(H_b,l_b).
--   $$
--
--   Projectively, $\mathrm{Roots}(H,l)$ lists the solutions of the homogeneous system $H=0$ in $\mathbb{P}^{|\iota|}$ inside the affine chart $\ell=1$; goodness says that no solution lies on the hyperplane $\ell=0$ and that every solution is nondegenerate. The theorem is the continuity half of a deformation argument: the number of solutions cannot change along a connected family of good systems, so it can be computed on a convenient model system.
--
--   **Formalization Note** The count is `Nat.card` (the number of elements of a finite type, and $0$ for an infinite one). The normalized system is `normalized (H t) (l t)`, with the linear equation at index `none`; the differentiability hypothesis is `ContDiff` of order $1$ over the complex numbers, and preconnectedness of $S$ is the instance `PreconnectedSpace S`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SmoothSlices.lean#L158-L177

import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms
import Definitions.Def_OAI_Algebra_Determinantal_PointBounds
import Definitions.Def_OAI_Algebra_Determinantal_ProjectiveCounts
import Definitions.Def_OAI_Algebra_Determinantal_KernelCharts
import Definitions.Def_OAI_Algebra_Determinantal_SchurDifferentials
import Definitions.Def_OAI_Algebra_Determinantal_SchurLifts
import Definitions.Def_OAI_Algebra_Determinantal_BilinearCounts
import Definitions.Def_OAI_Algebra_Determinantal_RegularSections
import Definitions.Def_OAI_Algebra_Determinantal_SmoothSlices

open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial Topology
open scoped Topology Classical
variable {ι : Type*} [Fintype ι]

theorem OAI.PermanentBorder.CI.normalized_count_constant (H : ℂ → ι → MvPolynomial (Option ι) ℂ)
    (l : ℂ → Option ι → ℂ) (e : ι → ℕ)
    (hh : ∀ t i, (H t i).IsHomogeneous (e i))
    (hc : ContDiff ℂ 1 (fun z : ℂ × (Option ι → ℂ) =>
      fun i => eval z.2 (normalized (H z.1) (l z.1) i)))
    (s : Set ℂ) [PreconnectedSpace s] (hg : ∀ t ∈ s, Good (H t) (l t))
    (a b : s) :
    Nat.card (Roots (H a.val) (l a.val)) = Nat.card (Roots (H b.val) (l b.val)) := by sorry
