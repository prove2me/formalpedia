-- Prove2me | Theorems.Thm_OAI_PermanentBorder_KernelBilinear_affine_polar_count
-- name    : OAI.PermanentBorder.KernelBilinear.affine_polar_count
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:45:38.414879+00:00
-- url     : https://prove2.me/theorems/d407f8e8-0696-4395-997f-536f15a87fd0
-- title:
--   Bézout-type bound $2^{m}\binom{2n+1}{m+1}$ for simple polar points of a determinantal pencil on an affine slice
-- statement:
--   Let $n\ge0$, let $\sigma,\kappa,J$ be finite sets, and put $m=|\kappa|$. Let $A_0$ and $A_v$ ($v\in\sigma$) be complex $(n+1)\times(n+1)$ matrices and let
--   $$f(y)=\det\Big(A_0+\sum_{v\in\sigma}y_vA_v\Big),\qquad y\in\mathbb{C}^{\sigma},$$
--   be the determinant of the affine matrix pencil. Let $b\in\mathbb{C}^{\sigma}$, let $\Lambda:\mathbb{C}^{\{\star\}\sqcup\kappa}\to\mathbb{C}^{\sigma}$ be a linear map, and let $\psi:\mathbb{C}\times\mathbb{C}^{\kappa}\to\mathbb{C}^{\sigma}$ be the affine map $\psi(z_\star,(z_k)_{k\in\kappa})=b+\Lambda(z_\star,(z_k)_k)$, which parametrises an affine slice of dimension at most $m+1$. Let $h_k\in\mathbb{C}^{\sigma}$ ($k\in\kappa$) be directions and define the polar map
--   $$\mathcal P(z)=\Big(f(\psi(z)),\ \big(Df(\psi(z))[h_k]\big)_{k\in\kappa}\Big)\in\mathbb{C}\times\mathbb{C}^{\kappa}.$$
--   If $x:J\to\mathbb{C}\times\mathbb{C}^{\kappa}$ is injective and every $x_j$ is a simple zero of $\mathcal P$, i.e. $\mathcal P(x_j)=0$ and the derivative $D\mathcal P(x_j)$ is invertible, then
--
--   $$
--   |J|\;\le\;2^{m}\binom{2n+1}{m+1}.
--   $$
--
--   So the number of nondegenerate points of the slice at which the determinant and its $m$ directional derivatives all vanish is bounded by an explicit quantity that depends only on the matrix size $n+1$ and on $m$, not on the number of variables $|\sigma|$ or on the matrices. It is the counting upper bound used for polynomials that are (limits of) determinants of $(n+1)\times(n+1)$ affine matrices: comparing it with the number of simple polar points such a polynomial must have yields lower bounds on the matrix size.
--
--   **Formalization Note** The pencil is `affine A₀ A y`, the linear map is a continuous linear map `(Option κ → ℂ) →L[ℂ] (σ → ℂ)` applied after `optionProduct.symm`, which identifies $\mathbb{C}\times\mathbb{C}^{\kappa}$ with $\mathbb{C}^{\{\star\}\sqcup\kappa}$; the polar map is `polarPair (fun y => (affine A₀ A y).det) ψ h`, and invertibility is `ContinuousLinearMap.IsInvertible` of `fderiv ℂ`. The matrices are indexed by `Fin (n+1)`, so in terms of the matrix size $N=n+1$ the bound reads $2^{m}\binom{2N-1}{m+1}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/Determinantal/BilinearCounts.lean#L333-L384

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

open OAI OAI.PermanentBorder OAI.PermanentBorder.KernelBilinear
open MvPolynomial Matrix PolarAnalysis PolarAnalysis.Schur
open scoped Classical
variable {σ κ J : Type} [Fintype σ] [Fintype κ] [Fintype J] {n : ℕ}

theorem OAI.PermanentBorder.KernelBilinear.affine_polar_count
    (A₀ : Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (A : σ → Matrix (Fin (n+1)) (Fin (n+1)) ℂ)
    (b : σ → ℂ) (L : (Option κ → ℂ) →L[ℂ] (σ → ℂ)) (h : κ → σ → ℂ)
    (x : J → ℂ × (κ → ℂ)) (hx : Function.Injective x)
    (hz : ∀ j, polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h (x j) = 0)
    (hs : ∀ j, (fderiv ℂ (polarPair (fun y => (affine A₀ A y).det)
      (fun z => b + L (optionProduct.symm z)) h) (x j)).IsInvertible) :
    Fintype.card J ≤ 2^Fintype.card κ * (2*n+1).choose (Fintype.card κ+1) := by sorry
