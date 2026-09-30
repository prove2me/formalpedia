-- Prove2me | Theorems.Thm_MakeToStockRM_ExpDensity_exponential_density_basic_adjoint_relation
-- name    : MakeToStockRM.ExpDensity.exponential_density_basic_adjoint_relation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:39:13.463344+00:00
-- url     : https://prove2.me/theorems/1af0eaef-1a61-4846-9948-e0755302a01c
-- title:
--   Proposition 2 (pinned down): the exponential density satisfies the basic adjoint relation (43) under conormal reflection $\Sigma\vec n$
-- statement:
--   Let $\theta\in\mathbb R$, $\sigma>0$, $\delta>0$, $-1<\varrho<1$, and let
--
--   $$
--   \Gamma=\theta\frac{\partial}{\partial x}+\frac{\sigma^2}{2}\frac{\partial^2}{\partial x^2}+\sigma\delta\varrho\frac{\partial^2}{\partial x\,\partial y}+\frac{\delta^2}{2}\frac{\partial^2}{\partial y^2}
--   $$
--
--   be the generator of the inventory/log-price diffusion $(\mathcal X,\mathcal Y)$, with covariance matrix $\Sigma=\begin{pmatrix}\sigma^2&\sigma\delta\varrho\\ \sigma\delta\varrho&\delta^2\end{pmatrix}$. Let $y_{\min}<y_{\max}$, let $\eta,\xi:\mathbb R\to\mathbb R$ be continuously differentiable with $\eta(y)<\xi(y)$ for all $y\in[y_{\min},y_{\max}]$, and let $\Omega=\{(x,y):y_{\min}<y<y_{\max},\ \eta(y)<x<\xi(y)\}$ (34), with inward unit normal $\vec n$ on $\partial\Omega$. Let $\pi(x,y)=\exp(m_xx+m_yy)$ with the exponents (47), $m_x=\frac{2\theta}{\sigma^2(1-\varrho^2)}$, $m_y=\frac{-2\varrho\theta}{\sigma\delta(1-\varrho^2)}$. Then for every twice continuously differentiable $f:\mathbb R^2\to\mathbb R$,
--
--   $$
--   \int_\Omega \Gamma f\;\pi\,ds+\frac12\int_{\partial\Omega}(\Sigma\vec n)\cdot\nabla f\;\pi\,dl=0,
--   $$
--
--   where $ds$ is Lebesgue measure on $\Omega$ and $dl$ is arc length on $\partial\Omega$. On the four pieces (35), $\vec n\,dl$ is $(1,-\eta'(y))\,dy$ on $x=\eta(y)$, $(-1,\xi'(y))\,dy$ on $x=\xi(y)$, $(0,1)\,dx$ on $y=y_{\min}$ and $(0,-1)\,dx$ on $y=y_{\max}$.
--
--   The paper's basic adjoint relation (43) reads $\int_\Omega\Gamma f\,\pi_\Omega\,ds+\frac12\int_{\partial\Omega}\vec v\cdot\nabla f\,\pi_\Omega\,dl=0$ for all test functions $f$ twice continuous and bounded, and it characterizes the stationary distribution $\pi_\Omega$ of the diffusion reflected along $\vec v$ (Harrison and Williams 1987). Proposition 2 asserts that when $T\vec v$ is normal to $\partial\Omega^*$ the stationary density is $K_\Omega e^{m_xx+m_yy}$. The theorem states that analytic content: with the reflection field $\vec v=\Sigma\vec n$, which is the field singled out by the hypothesis of Proposition 2, the exponential density satisfies (43).
--
--   **Formalization Note** This is a pinned-down version of Proposition 2, whose proof is in an online companion not available here. (i) The paper does not fix the length of $\vec v$; its hypothesis "$T\vec v$ is normal to $\partial\Omega^*$" fixes only the direction $\vec v\parallel\Sigma\vec n$ (see the whitening milestone), and among these fields (43) holds for this density only with $\vec v=\Sigma\vec n$ ($\vec n$ the unit normal, $dl$ arc length). The page's phrase "substituting the inward unit normal vector field $\vec n$ … for $\vec v$" would give a false statement unless $\Sigma$ is a multiple of the identity. (ii) The normalizing constant $K_\Omega$ is omitted because (43) is linear in $\pi$; its existence is a separate milestone. (iii) The step "BAR implies stationary law" (Harrison–Williams) is not formalized. (iv) Test functions are all $C^2$ functions on $\mathbb R^2$; on the bounded closure of $\Omega$ they and their derivatives are bounded, which is the paper's "twice continuous and bounded". (v) The curves are $C^1$ on all of $\mathbb R$; only their values on $[y_{\min},y_{\max}]$ enter, and a $C^1$ function on a closed interval extends to $\mathbb R$. (vi) The mixed partial in $\Gamma$ is $\partial_x(\partial_yf)$. All integrands are continuous on compact sets, so no integral takes Lean's junk value $0$.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, Proposition 2 with eq. (47) and the basic adjoint relation (43); region and boundary (34)–(35), p. 866; generator Γ, p. 865

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_generator
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity
import Definitions.Def_MakeToStockRM_ExpDensity_region
import Definitions.Def_MakeToStockRM_ExpDensity_boundaryTerm

namespace MakeToStockRM.ExpDensity

theorem exponential_density_basic_adjoint_relation (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (f : ℝ × ℝ → ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1) (hy : ymin < ymax)
    (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y)
    (hf : ContDiff ℝ 2 f) :
    (∫ z in region η ξ ymin ymax, generator θ σ δ ϱ f z * expDensity θ σ δ ϱ z)
      + 1 / 2 * boundaryTerm σ δ ϱ η ξ ymin ymax f (expDensity θ σ δ ϱ) = 0 := by sorry

end MakeToStockRM.ExpDensity
