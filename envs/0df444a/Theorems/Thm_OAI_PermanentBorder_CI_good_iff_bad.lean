-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CI_good_iff_bad
-- name    : OAI.PermanentBorder.CI.good_iff_bad
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:46:50.189658+00:00
-- url     : https://prove2.me/theorems/ef8ae81b-711c-4769-a28c-0f44331ac4de
-- title:
--   A system is regular with respect to a linear form iff an enlarged system has only the trivial zero
-- statement:
--   Let $K$ be a field and $\iota$ a finite set, and write $\hat\iota=\{\star\}\sqcup\iota$. Let $H_i\in K[y_j:j\in\hat\iota]$ ($i\in\iota$) be polynomials, one fewer than the number of variables, and let $l\in K^{\hat\iota}$ define the linear form $\ell(y)=\sum_{j\in\hat\iota}l_jy_j$. Let $J_{H,l}$ be the square matrix of polynomials with rows and columns indexed by $\hat\iota$ whose row $\star$ is the constant row $(l_j)_j$ and whose row $i\in\iota$ is the formal gradient $\big(\partial H_i/\partial y_j\big)_j$. Call the pair $(H,l)$ *good* if every nonzero common zero is off the hyperplane $\ell=0$ and nondegenerate:
--   $$\forall\,y\in K^{\hat\iota}\setminus\{0\}:\qquad\big(H_i(y)=0\ \ \forall i\in\iota\big)\ \Longrightarrow\ \ell(y)\neq0\ \text{ and }\ \det J_{H,l}(y)\neq0 .$$
--   Then $(H,l)$ is good if and only if the enlarged system has only the trivial zero:
--
--   $$
--   (H,l)\ \text{good}\iff\Big[\ \forall\,y\in K^{\hat\iota}:\ \big(H_i(y)=0\ \ \forall i\in\iota\ \text{ and }\ \ell(y)\det J_{H,l}(y)=0\big)\ \Rightarrow\ y=0\ \Big].
--   $$
--
--   When the $H_i$ are homogeneous, goodness says that the projective zero set of the $H_i$ avoids the hyperplane $\ell=0$ and consists of points at which the Jacobian, bordered by the row of $\ell$, is invertible. The equivalence recasts this geometric condition as the statement that the explicit polynomials $H_i$ and $\ell\cdot\det J_{H,l}$ have no common zero other than $0$, a form in which it can be certified algebraically.
--
--   **Formalization Note** The variables are indexed by `Option ι`, with `none` playing the role of $\star$; $J_{H,l}$ is `square H l`, evaluated entrywise by `Matrix.map (eval y)` before taking the determinant; the predicate is `Good H l`; and the enlarged family is `bad H l`, with `bad H l none` $=\ell\cdot\det J_{H,l}$ and `bad H l (some i)` $=H_i$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RegularSections.lean#L82-L98

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
variable {K ι : Type*} [Field K] [Fintype ι]

theorem OAI.PermanentBorder.CI.good_iff_bad (H : ι → MvPolynomial (Option ι) K) (l : Option ι → K) :
    Good H l ↔ ∀ y : Option ι → K, (∀ i, eval y (bad H l i) = 0) → y = 0 := by sorry
