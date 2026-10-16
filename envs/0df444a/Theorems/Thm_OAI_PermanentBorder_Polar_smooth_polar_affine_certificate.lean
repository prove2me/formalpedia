-- Prove2me | Theorems.Thm_OAI_PermanentBorder_Polar_smooth_polar_affine_certificate
-- name    : OAI.PermanentBorder.Polar.smooth_polar_affine_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T23:13:43.56938+00:00
-- url     : https://prove2.me/theorems/611850b8-9bd7-41bb-85bd-8db7fe087323
-- title:
--   A smooth form of degree $r$ and $m$ polars have $r(r-1)^m$ distinct nondegenerate zeros in an affine chart
-- statement:
--   Let $\tau$ be a finite set with $m$ elements, $U=\{\ast\}\sqcup\tau$ and $V=\{\star\}\sqcup U$, so $|U|=m+1$ and $|V|=m+2$. Let $f\in\mathbb{C}[X_v : v\in V]$ be homogeneous of degree $r\ge2$ and *smooth*: the only $y\in\mathbb{C}^V$ with $f(y)=0$ and $\partial_vf(y)=0$ for all $v\in V$ is $y=0$. For directions $w=(w_{iv})_{i\in\tau,\,v\in V}$ in $\mathbb{C}$ consider the $m+1$ polynomials
--   $$
--   h_\ast=f,\qquad h_i=\sum_{v\in V}w_{iv}\,\partial_vf\quad(i\in\tau),
--   $$
--   i.e. $f$ and its polars in the directions $w_i$. For a linear automorphism $e$ of $\mathbb{C}^V$ define the affine chart $\phi_e:\mathbb{C}^U\to\mathbb{C}^V$ by $\phi_e(z)=e^{-1}(\hat z)$, where $\hat z_\star=1$ and $\hat z_u=z_u$ for $u\in U$. Then, with $N=r(r-1)^m$, there exist directions $w$, a continuous linear automorphism $e$ of $\mathbb{C}^V$ and pairwise distinct points $x_1,\dots,x_N\in\mathbb{C}^U$ such that, for every $k$, the square system $F_{w,e}(z)=\big(h_u(\phi_e(z))\big)_{u\in U}$ on $\mathbb{C}^U$ satisfies
--   $$
--   F_{w,e}(x_k)=0\qquad\text{and}\qquad DF_{w,e}(x_k):\mathbb{C}^U\to\mathbb{C}^U\ \text{is invertible.}
--   $$
--
--   Thus a smooth form of degree $r$ in $m+2$ variables, together with $m$ suitably chosen polars, has at least $r(r-1)^m$ distinct nondegenerate common zeros. They are presented as simple zeros of a square polynomial system in $m+1$ affine coordinates. Explicit families of nondegenerate zeros of this kind are the algebraic input for lower bounds on the size of (border) determinantal representations of polynomials whose lowest-degree form at a point is smooth.
--
--   **Formalization Note** $V$ is `PolarVars τ = Option (Option τ)` and $U$ is `Option τ`, with $\star$ = `none` in $V$ and $\ast$ = `none` in $U$. The polynomials $h_u$ are `hypersurfacePolars w f u`, the chart is `affineNormChart e`, the points are an injective map `Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ`, and the derivative is the Fréchet derivative `fderiv` over the complex numbers, required to be `IsInvertible`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/Model.lean#L59-L111

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
import Definitions.Def_OAI_Algebra_Determinantal_RankTransfer
import Definitions.Def_OAI_Algebra_Determinantal_Model

open OAI OAI.PermanentBorder OAI.PermanentBorder.Polar
open MvPolynomial
open scoped Classical
variable {τ : Type*} [Fintype τ]

theorem OAI.PermanentBorder.Polar.smooth_polar_affine_certificate (f : MvPolynomial (PolarVars τ) ℂ)
    {r : ℕ} (hr : 2 ≤ r) (hh : f.IsHomogeneous r)
    (hs : ∀ y : PolarVars τ → ℂ, eval y f = 0 →
      (∀ j, eval y (pderiv j f) = 0) → y = 0) :
    ∃ w : τ → PolarVars τ → ℂ,
    ∃ e : (PolarVars τ → ℂ) ≃L[ℂ] (PolarVars τ → ℂ),
    ∃ x : Fin (r * (r-1)^Fintype.card τ) → Option τ → ℂ,
      Function.Injective x ∧
      ∀ i, (fun j => eval (affineNormChart e (x i)) (hypersurfacePolars w f j)) = 0 ∧
        (fderiv ℂ (fun z j => eval (affineNormChart e z)
          (hypersurfacePolars w f j)) (x i)).IsInvertible := by sorry
