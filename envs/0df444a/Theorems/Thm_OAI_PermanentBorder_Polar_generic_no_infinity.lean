-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_generic_no_infinity
-- name    : OAI.PermanentBorder.Polar.generic_no_infinity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:06:36.740668+00:00
-- url     : https://prove2.me/theorems/3a663167-5449-49f6-9ac3-e0bc467452c8
-- title:
--   Smooth points cut out by generic polars avoid the generic hyperplane
-- statement:
--   Let $K$ be a field of characteristic zero, $\tau$ a finite set and $V=\{\star,\ast\}\sqcup\tau$. Let $\tau_\circ=\{\circ\}\sqcup\tau$ and $\mathcal{P}=\tau_\circ\times V$. Let $(u_p)_{p\in\mathcal{P}}$ be independent indeterminates and $E$ an algebraic closure of the rational function field $K(u_p : p\in\mathcal{P})$. The *generic directions* and the *generic linear form* are
--   $$
--   w_{iv}=u_{(i,v)}\quad(i\in\tau,\ v\in V),\qquad l_v=u_{(\circ,v)}\quad(v\in V).
--   $$
--   Let $f\in K[X_v : v\in V]$ be homogeneous of degree $r\in\mathbb{N}$. Write $\partial_vf(y)$ for partial derivatives evaluated at $y\in E^V$, and $\Pi_i(y)=\sum_{v\in V}w_{iv}\,\partial_vf(y)$ for the generic polars. Then for every $y\in E^V$
--   $$
--   f(y)=0,\quad \Pi_i(y)=0\ \ (i\in\tau),\quad \partial_vf(y)\ne0\ \text{for some } v,\quad \sum_{v\in V}l_v\,y_v=0\qquad\Longrightarrow\qquad y=0 .
--   $$
--   Equivalently, no nonzero point satisfies all four conditions.
--
--   Projectively: at a point of the hypersurface $f=0$ where the gradient does not vanish, the hypersurface and its $|\tau|$ generic polar hypersurfaces never meet on the generic hyperplane $\ell=0$. When the gradient of $f$ vanishes at no nonzero common zero (as for a smooth form), this means that no projective solution of the generic polar system lies on the hyperplane $\ell=0$, so all solutions lie in the affine chart $\ell=1$.
--
--   **Formalization Note** $E$ is `GenericField K P`, i.e. `AlgebraicClosure (FractionRing (MvPolynomial P K))` with `P = Option τ × PolarVars τ`; $u_p$ is `genericParameter K P p`, and $w$, $l$ are `genericDirections` and `genericLinear`. The index set $V$ is `PolarVars τ = Option (Option τ)` (with $\star$ = `none` and $\ast$ = `some none`), the index $\circ$ is `none` in `Option τ`, and $f$ is evaluated at $y$ with `aeval`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/GenericPolars.lean#L229-L245

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

theorem OAI.PermanentBorder.Polar.generic_no_infinity (f : MvPolynomial (PolarVars τ) K) {r : ℕ}
    (hhom : f.IsHomogeneous r) (y : PolarVars τ → E)
    (hf : aeval y f = 0) (hp : ∀ i, polarValue genericDirections f y i = 0)
    (hg : ∃ j, aeval y (pderiv j f) ≠ 0)
    (hn : ∑ j, genericLinear j * y j = 0) : y = 0 := by sorry
