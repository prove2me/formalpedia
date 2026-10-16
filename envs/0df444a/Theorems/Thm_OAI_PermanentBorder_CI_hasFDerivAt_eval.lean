-- Prove2me | Theorems.Thm_OAI_PermanentBorder_CI_hasFDerivAt_eval
-- name    : OAI.PermanentBorder.CI.hasFDerivAt_eval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:49:14.924152+00:00
-- url     : https://prove2.me/theorems/a1a48a36-8169-480b-b492-ab85cfe15fce
-- title:
--   The Fréchet derivative of a complex polynomial function is given by its formal partial derivatives
-- statement:
--   Let $\sigma$ be a finite set, let $p\in\mathbb{C}[y_s:s\in\sigma]$ be a polynomial and $x\in\mathbb{C}^{\sigma}$. Then the polynomial function $y\mapsto p(y)$ on $\mathbb{C}^{\sigma}$ has Fréchet derivative at $x$ equal to the linear functional built from the formal partial derivatives of $p$:
--
--   $$
--   Dp(x)[w]=\sum_{s\in\sigma}\frac{\partial p}{\partial y_s}(x)\,w_s\qquad(w\in\mathbb{C}^{\sigma}),
--   $$
--
--   that is, $p(x+w)=p(x)+\sum_s\frac{\partial p}{\partial y_s}(x)\,w_s+o(\|w\|)$ as $w\to0$.
--
--   The result connects algebraic and analytic differentiation: the Jacobian matrix of a polynomial map, computed with formal partial derivatives, is the matrix of its Fréchet derivative. This lets nondegeneracy conditions stated algebraically, such as the nonvanishing of a Jacobian determinant, be used in analytic arguments such as the inverse and implicit function theorems.
--
--   **Formalization Note** The functional is `polynomialDerivative p x` $=\sum_s(\partial_sp)(x)\cdot\mathrm{pr}_s$, where $\partial_s$ is the formal derivative `pderiv s` and $\mathrm{pr}_s$ the coordinate projection; the claim is `HasFDerivAt`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/RegularSections.lean#L222-L249

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
open MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem OAI.PermanentBorder.CI.hasFDerivAt_eval (p : MvPolynomial σ ℂ) (x : σ → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (polynomialDerivative p x) x := by sorry
