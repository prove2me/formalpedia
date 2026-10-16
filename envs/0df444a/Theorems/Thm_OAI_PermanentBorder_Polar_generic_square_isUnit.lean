-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_generic_square_isUnit
-- name    : OAI.PermanentBorder.Polar.generic_square_isUnit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:09:19.42408+00:00
-- url     : https://prove2.me/theorems/7e6614c8-779e-48af-8cf6-6824428866f9
-- title:
--   The polar Jacobian with generic directions and linear form is invertible at smooth common zeros
-- statement:
--   Let $K$ be a field of characteristic zero, $\tau$ a finite set and $V=\{\star,\ast\}\sqcup\tau$. Let $\tau_\circ=\{\circ\}\sqcup\tau$ and $\mathcal{P}=\tau_\circ\times V$. Let $(u_p)_{p\in\mathcal{P}}$ be independent indeterminates and $E$ an algebraic closure of $K(u_p : p\in\mathcal{P})$. Take the generic directions $w_{iv}=u_{(i,v)}$ ($i\in\tau$, $v\in V$) and the generic linear form $l_v=u_{(\circ,v)}$ ($v\in V$). Let $f\in K[X_v : v\in V]$ be homogeneous of degree $r\in\mathbb{N}$, and for $y\in E^V$ write $\Pi_i(y)=\sum_vw_{iv}\,\partial_vf(y)$ and $G_{iv}=\sum_kw_{ik}\,\partial_v\partial_kf(y)$. Let $Q(y)$ be the $V\times V$ matrix with rows
--   $$
--   Q_{\star v}=\partial_vf(y),\qquad Q_{\ast v}=l_v,\qquad Q_{iv}=G_{iv}\quad(i\in\tau).
--   $$
--   If $y\in E^V$ satisfies $f(y)=0$, $\Pi_i(y)=0$ for all $i\in\tau$, $y\ne0$, and $\partial_vf(y)\ne0$ for some $v\in V$, then
--   $$
--   Q(y)\ \text{is invertible.}
--   $$
--
--   In projective terms: at every common zero of $f$ and its $|\tau|$ generic polars where $f$ has a nonvanishing gradient, the polar system together with the generic linear form is nondegenerate. For a smooth form $f$, combined with the absence of solutions on the hyperplane $\ell=0$, this shows that the bad locus of the polar system is empty for generic parameters. A Macaulay-matrix certificate then transfers this conclusion to explicit complex parameters.
--
--   **Formalization Note** $E$ is `GenericField K P` with `P = Option τ × PolarVars τ`, $Q(y)$ is `squareJacobian genericDirections genericLinear f y`, and invertibility is `IsUnit`. Here $V$ is `PolarVars τ = Option (Option τ)`, with $\star$ = `none` and $\ast$ = `some none`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/GenericPolars.lean#L247-L275

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
variable {K τ : Type*} [Field K] [CharZero K] [Fintype τ] [DecidableEq τ]
local notation "P" => (Option τ × PolarVars τ)
local notation "E" => GenericField K P

theorem OAI.PermanentBorder.Polar.generic_square_isUnit (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hy : y ≠ 0) (hg : ∃ j, aeval y (pderiv j f) ≠ 0) :
    IsUnit (squareJacobian genericDirections genericLinear f y) := by sorry
