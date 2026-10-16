-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_square_isUnit_of_independent
-- name    : OAI.PermanentBorder.Polar.square_isUnit_of_independent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:05:05.876362+00:00
-- url     : https://prove2.me/theorems/63b676c6-b77a-457f-a0b5-1873b2230a96
-- title:
--   Independence of the gradient, polar gradients and linear form makes the square polar Jacobian invertible
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $\tau$ be a finite set and $V=\{\star,\ast\}\sqcup\tau$, an index set with $|\tau|+2$ elements. Let $f\in K[X_v : v\in V]$, $y\in L^V$, $w=(w_{iv})_{i\in\tau,\,v\in V}$ with entries in $L$, and $l\in L^V$. Write $\partial_vf(y)$ for partial derivatives evaluated at $y$ (through $K\to L$) and $G_{iv}=\sum_{k\in V}w_{ik}\,\partial_v\partial_kf(y)$ for the polar gradients. Let $Q$ be the square matrix indexed by $V\times V$ with rows
--   $$
--   Q_{\star v}=\partial_vf(y),\qquad Q_{\ast v}=l_v,\qquad Q_{iv}=G_{iv}\quad(i\in\tau,\ v\in V).
--   $$
--   Assume that these rows are linearly independent in the following sense: whenever $c,z\in L$ and $\gamma\in L^\tau$ satisfy $c\,\partial_vf(y)+\sum_{i\in\tau}\gamma_iG_{iv}+z\,l_v=0$ for all $v\in V$, then $c=0$, $z=0$ and $\gamma=0$. Then $Q$ is invertible:
--   $$
--   Q\in GL_V(L).
--   $$
--
--   The matrix $Q$ collects the gradient of $f$, the linear form $l$ and the gradients of the polars $\sum_kw_{ik}\partial_kf$ at $y$. Its invertibility is the nondegeneracy condition for a common zero of $f$ and its polars in the chart cut out by $l$. The lemma converts the independence statements obtained from derivation arguments into this matrix form.
--
--   **Formalization Note** $V$ is `PolarVars τ = Option (Option τ)`, with $\star$ the index `none` and $\ast$ the index `some none`. $Q$ is `squareJacobian w l f y`, and invertibility is `IsUnit` in the ring of square matrices over $L$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/GenericPolars.lean#L165-L184

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
import Definitions.Def_OAI_Algebra_Determinantal_GenericPolars

open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open MvPolynomial Matrix
variable {K L τ : Type*} [Field K] [Field L] [Algebra K L] [Fintype τ]

theorem OAI.PermanentBorder.Polar.square_isUnit_of_independent [DecidableEq τ]
    (w : τ → PolarVars τ → L) (l : PolarVars τ → L)
    (f : MvPolynomial (PolarVars τ) K) (y : PolarVars τ → L)
    (h : ∀ (c z : L) (cfs : τ → L), (∀ j, c * aeval y (pderiv j f) +
      ∑ i, cfs i * polarGradient w f y i j + z * l j = 0) →
      c = 0 ∧ z = 0 ∧ cfs = 0) : IsUnit (squareJacobian w l f y) := by sorry
