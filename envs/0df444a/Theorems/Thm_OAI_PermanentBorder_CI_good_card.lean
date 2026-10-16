-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CI_good_card
-- name    : OAI.PermanentBorder.CI.good_card
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:01:48.560347+00:00
-- url     : https://prove2.me/theorems/24247760-d67c-48a7-994b-133a5f910f6c
-- title:
--   Bézout count for good homogeneous systems: the number of affine roots is the product of the degrees
-- statement:
--   Let $\iota$ be a finite set and $\iota_\ast=\{\ast\}\sqcup\iota$, and consider complex polynomials in the variables $X_j$, $j\in\iota_\ast$. Let $H=(H_i)_{i\in\iota}$ be such polynomials, with $H_i$ homogeneous of degree $e_i\ge1$. Let $l\in\mathbb{C}^{\iota_\ast}$ with associated linear form $\ell(y)=\sum_{j\in\iota_\ast}l_jy_j$. Assume that $(H,l)$ is *good*: every common zero $y\ne0$ of the $H_i$ satisfies $\ell(y)\ne0$ and $\det J(y)\ne0$. Here $J(y)$ is the $\iota_\ast\times\iota_\ast$ matrix whose row $\ast$ is $(l_j)_{j\in\iota_\ast}$ and whose row $i\in\iota$ is the gradient $(\partial_jH_i(y))_{j\in\iota_\ast}$. Then the number of roots in the affine chart $\ell=1$ is the product of the degrees:
--   $$
--   \#\{y\in\mathbb{C}^{\iota_\ast} : H_i(y)=0\ \text{for all } i\in\iota,\ \ell(y)=1\}=\prod_{i\in\iota}e_i .
--   $$
--
--   This is Bézout's theorem for $|\iota|$ homogeneous equations in $\mathbb{P}^{|\iota|}$ in the nondegenerate situation. If no solution lies on the hyperplane $\ell=0$, every projective solution has exactly one representative with $\ell(y)=1$. If moreover all solutions are nondegenerate, there are exactly $\prod_ie_i$ of them. It is the counting tool used to show that a smooth form of degree $r$ and $m$ suitably chosen polars have exactly $r(r-1)^m$ common zeros in an affine chart.
--
--   **Formalization Note** The left-hand side is `Nat.card (Roots H l)`. Goodness is the predicate `Good H l`, where the matrix $J$ is `square H l` evaluated at $y$. When $\iota$ is empty the product is $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/SliceCertificates.lean#L259-L273

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
import Definitions.Def_OAI_Algebra_Determinantal_SliceCertificates

open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem OAI.PermanentBorder.CI.good_card (H : ι → MvPolynomial (Option ι) ℂ) (l : Option ι → ℂ)
    (e : ι → ℕ) (he : ∀ i, 0 < e i) (hh : ∀ i, (H i).IsHomogeneous (e i))
    (hg : Good H l) : Nat.card (Roots H l) = ∏ i, e i := by sorry
