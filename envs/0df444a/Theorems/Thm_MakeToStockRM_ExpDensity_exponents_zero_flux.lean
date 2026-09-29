-- Prove2me | Theorems.Thm_MakeToStockRM_ExpDensity_exponents_zero_flux
-- name    : MakeToStockRM.ExpDensity.exponents_zero_flux
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:37:30.750763+00:00
-- url     : https://prove2.me/theorems/c35233a3-3019-4203-af46-e157dbb75dc3
-- title:
--   (47): zero-flux identity $\tfrac12\Sigma\nabla p=(\theta,0)\,p$
-- statement:
--   Let $\theta\in\mathbb R$, $\sigma>0$, $\delta>0$, $-1<\varrho<1$, let $\Sigma=\begin{pmatrix}\sigma^2&\sigma\delta\varrho\\ \sigma\delta\varrho&\delta^2\end{pmatrix}$ be the covariance matrix of the inventory/log-price diffusion, and let $p(x,y)=\exp(m_xx+m_yy)$ with the exponents (47), $m_x=\frac{2\theta}{\sigma^2(1-\varrho^2)}$, $m_y=\frac{-2\varrho\theta}{\sigma\delta(1-\varrho^2)}$. Then at every point $z\in\mathbb R^2$
--
--   $$
--   \tfrac12\,\Sigma\,\nabla p(z)=\begin{pmatrix}\theta\,p(z)\\ 0\end{pmatrix},
--   $$
--
--   that is, $\sigma^2m_x+\sigma\delta\varrho\,m_y=2\theta$ and $\sigma\delta\varrho\,m_x+\delta^2m_y=0$.
--
--   The probability flux of the diffusion with density $p$ is $(\theta,0)p-\tfrac12\Sigma\nabla p$; the identity says it vanishes identically. This is what makes the boundary terms involving $f$ itself drop out of the basic adjoint relation (43), leaving only the conormal term $\tfrac12\int_{\partial\Omega}(\Sigma\vec n)\cdot\nabla f\,p\,dl$.
--
--   **Formalization Note** Part of the analytic content of Proposition 2 (proof in an online companion not available here). $\nabla p=(\partial_xp,\partial_yp)$ with Fréchet partial derivatives; $\Sigma$ acts on column vectors indexed by `Fin 2`, inventory first.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, Proposition 2, eq. (47); covariance from Γ, p. 865

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity

namespace MakeToStockRM.ExpDensity

open Matrix

theorem exponents_zero_flux (θ σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) :
    ∀ z : ℝ × ℝ,
      (1 / 2 : ℝ) • (covMatrix σ δ ϱ *ᵥ
          ![partialX (expDensity θ σ δ ϱ) z, partialY (expDensity θ σ δ ϱ) z])
        = ![θ * expDensity θ σ δ ϱ z, 0] := by sorry

end MakeToStockRM.ExpDensity
