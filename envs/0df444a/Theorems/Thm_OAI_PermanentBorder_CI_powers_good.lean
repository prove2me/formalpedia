-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CI_powers_good
-- name    : OAI.PermanentBorder.CI.powers_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:47:26.747481+00:00
-- url     : https://prove2.me/theorems/6ac111ea-fafe-49fe-a397-dc2b3a1a7eaf
-- title:
--   The power system $y_i^{e_i}=y_\star^{e_i}$ is good with respect to the coordinate $y_\star$
-- statement:
--   Let $\iota$ be a finite set, $\hat\iota=\{\star\}\sqcup\iota$, and let $e_i\ge1$ ($i\in\iota$) be positive integers. Consider the polynomials
--   $$H_i=y_i^{e_i}-y_\star^{e_i}\in\mathbb{C}[y_j:j\in\hat\iota]\qquad(i\in\iota)$$
--   and the linear form $\ell(y)=y_\star$, whose coefficient vector is the indicator of $\star$. Let $J(y)$ be the $\hat\iota\times\hat\iota$ matrix whose row $\star$ is the coefficient vector $(1,0,\dots,0)$ of $\ell$ and whose row $i$ is the gradient of $H_i$ at $y$: the entry $-e_iy_\star^{e_i-1}$ in column $\star$, the entry $e_iy_i^{e_i-1}$ in column $i$, and $0$ elsewhere. Then the pair $(H,\ell)$ is good, that is,
--
--   $$
--   \forall\,y\in\mathbb{C}^{\hat\iota}\setminus\{0\}:\qquad\big(y_i^{e_i}=y_\star^{e_i}\ \ \forall i\in\iota\big)\ \Longrightarrow\ y_\star\neq0\ \text{ and }\ \det J(y)\neq0 .
--   $$
--
--   In the affine chart $y_\star=1$ the solutions are the tuples $(y_i)_{i\in\iota}$ with each $y_i$ an $e_i$-th root of unity, so there are exactly $\prod_ie_i$ of them; the theorem says that no projective solution lies at infinity and that all solutions are nondegenerate. This makes the power system a model good system of homogeneous equations of degrees $e_i$, against which other good systems with the same degrees can be compared.
--
--   **Formalization Note** The system is `powers e`, the linear form is given by `coordinate = Pi.single none 1`, and goodness is the predicate `Good`, whose determinant condition is stated for the matrix of polynomials `square H l` evaluated entrywise at $y$. The exponent $e_i-1$ is natural-number subtraction, harmless here since $e_i\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RegularSections.lean#L120-L169

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

open OAI OAI.PermanentBorder OAI.PermanentBorder.CI
open MvPolynomial Matrix
open scoped Classical
variable {ι : Type*} [Fintype ι]

theorem OAI.PermanentBorder.CI.powers_good (e : ι → ℕ) (he : ∀ i, 0 < e i) : Good (powers e) coordinate := by sorry
