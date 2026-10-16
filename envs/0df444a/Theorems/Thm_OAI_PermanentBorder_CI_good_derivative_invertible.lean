-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CI_good_derivative_invertible
-- name    : OAI.PermanentBorder.CI.good_derivative_invertible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:53:10.712646+00:00
-- url     : https://prove2.me/theorems/bb3c7ff7-04c5-4b64-9cd3-b6d0524b1116
-- title:
--   Normalised roots of a good polynomial system are nondegenerate
-- statement:
--   Let $\iota$ be a finite set and $\hat\iota=\{\star\}\sqcup\iota$, let $H_i\in\mathbb{C}[y_j:j\in\hat\iota]$ ($i\in\iota$) be polynomials, and let $l\in\mathbb{C}^{\hat\iota}$ with linear form $\ell(y)=\sum_jl_jy_j$. Let $J_{H,l}$ be the $\hat\iota\times\hat\iota$ matrix of polynomials whose row $\star$ is $(l_j)_j$ and whose row $i$ is the formal gradient $(\partial H_i/\partial y_j)_j$, and suppose that $(H,l)$ is *good*: every nonzero $y$ with $H_i(y)=0$ for all $i$ satisfies $\ell(y)\neq0$ and $\det J_{H,l}(y)\neq0$. Consider the normalised square system
--   $$N:\mathbb{C}^{\hat\iota}\to\mathbb{C}^{\hat\iota},\qquad N(y)_\star=\ell(y)-1,\qquad N(y)_i=H_i(y)\ \ (i\in\iota).$$
--   If $N(y)=0$ at a point $y\in\mathbb{C}^{\hat\iota}$, then
--
--   $$
--   DN(y):\mathbb{C}^{\hat\iota}\to\mathbb{C}^{\hat\iota}\ \text{ is invertible}.
--   $$
--
--   So every root of a good system in the affine chart $\ell=1$ is a nondegenerate root of the square system $N$. By the implicit function theorem such roots move continuously and locally injectively with parameters; this is the local half of the argument showing that good systems with the same degrees have the same number of normalised roots.
--
--   **Formalization Note** $N$ is `fun y i => eval y (normalized H l i)`, with `normalized H l none = linear l - 1` and `normalized H l (some i) = H i`; goodness is the predicate `Good H l`; invertibility is `ContinuousLinearMap.IsInvertible` of `fderiv ℂ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SmoothSlices.lean#L43-L58

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

theorem OAI.PermanentBorder.CI.good_derivative_invertible (H : ι → MvPolynomial (Option ι) ℂ)
    (l y : Option ι → ℂ) (h : Good H l)
    (hy : (fun i => eval y (normalized H l i)) = 0) :
    (fderiv ℂ (fun y i => eval y (normalized H l i)) y).IsInvertible := by sorry
