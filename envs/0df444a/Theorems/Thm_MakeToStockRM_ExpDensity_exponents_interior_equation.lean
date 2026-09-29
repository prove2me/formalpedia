-- Prove2me | Theorems.Thm_MakeToStockRM_ExpDensity_exponents_interior_equation
-- name    : MakeToStockRM.ExpDensity.exponents_interior_equation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:37:00.779157+00:00
-- url     : https://prove2.me/theorems/f16a654a-47e9-4419-bc58-48ba295f33a8
-- title:
--   (47): the exponential density solves the interior adjoint equation $\Gamma^*p=0$
-- statement:
--   Let $\theta\in\mathbb R$, $\sigma>0$, $\delta>0$ and $-1<\varrho<1$. Let $m_x=\frac{2\theta}{\sigma^2(1-\varrho^2)}$ and $m_y=\frac{-2\varrho\theta}{\sigma\delta(1-\varrho^2)}$ be the exponents (47), and $p(x,y)=\exp(m_xx+m_yy)$. Then $p$ is annihilated by the formal adjoint of the generator of the inventory/log-price diffusion: for every $(x,y)\in\mathbb R^2$,
--
--   $$
--   -\theta\,\frac{\partial p}{\partial x}+\frac{\sigma^2}{2}\,\frac{\partial^2 p}{\partial x^2}+\sigma\delta\varrho\,\frac{\partial^2 p}{\partial x\,\partial y}+\frac{\delta^2}{2}\,\frac{\partial^2 p}{\partial y^2}=0 .
--   $$
--
--   Equivalently, $-\theta m_x+\frac{\sigma^2}{2}m_x^2+\sigma\delta\varrho\,m_xm_y+\frac{\delta^2}{2}m_y^2=0$. This is the interior half of the claim in Proposition 2 that the steady-state density of $(\mathcal X,\mathcal Y)$ is exponential: a stationary density must satisfy $\Gamma^*\pi=0$ inside $\Omega$.
--
--   **Formalization Note** This formalizes the interior part of the analytic content of Proposition 2, whose proof is in an online companion not available here; the probabilistic assertion that $\pi$ is the stationary law is not formalized. The mixed partial is $\partial_x(\partial_y p)$. The hypotheses $\sigma,\delta>0$, $|\varrho|<1$ are the paper's standing ones and keep the divisions in (47) nondegenerate. $\theta=0$ is allowed (then $p\equiv1$).
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, Proposition 2, eq. (47); generator Γ p. 865

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity

namespace MakeToStockRM.ExpDensity

theorem exponents_interior_equation (θ σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) :
    ∀ z : ℝ × ℝ, adjointGenerator θ σ δ ϱ (expDensity θ σ δ ϱ) z = 0 := by sorry

end MakeToStockRM.ExpDensity
