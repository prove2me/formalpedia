-- Prove2me | Theorems.Thm_MakeToStockRM_ExpDensity_normalizing_constant_exists
-- name    : MakeToStockRM.ExpDensity.normalizing_constant_exists
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T11:38:31.987608+00:00
-- url     : https://prove2.me/theorems/5d1d91e9-7943-47ba-991a-bb73e5e83f85
-- title:
--   Proposition 2: the normalizing constant $K_\Omega$ exists and is positive
-- statement:
--   Let $y_{\min}<y_{\max}$, let $\eta,\xi:\mathbb R\to\mathbb R$ be continuous with $\eta(y)<\xi(y)$ for every $y\in[y_{\min},y_{\max}]$, and let $\Omega=\{(x,y): y_{\min}<y<y_{\max},\ \eta(y)<x<\xi(y)\}$ be the region (34). Let $p(x,y)=\exp(m_xx+m_yy)$ be the exponential density with the exponents (47) for any parameters $\theta,\sigma,\delta,\varrho$. Then $p$ is Lebesgue integrable on $\Omega$, and there is exactly one constant $K_\Omega$ with
--
--   $$
--   K_\Omega>0\qquad\text{and}\qquad \int_\Omega K_\Omega\,e^{m_xx+m_yy}\,dx\,dy=1 .
--   $$
--
--   This is the clause of Proposition 2 that "$K_\Omega$ is a positive constant such that $\pi_\Omega$ integrates to one in $\Omega$": the density $\pi_\Omega=K_\Omega\,e^{m_xx+m_yy}$ is a probability density on $\Omega$.
--
--   **Formalization Note** The integral is the Lebesgue integral on $\mathbb R^2$ restricted to $\Omega$; integrability is asserted explicitly, so the value $0$ that Lean assigns to non-integrable functions cannot be what the statement is about. Continuity of the curves (weaker than the $C^1$ assumed in the goal) and $\eta<\xi$ on the closed interval guarantee $\Omega$ is bounded with positive area. Part of the analytic content of Proposition 2, whose proof is in an online companion not available here.
-- source:
--   Caldentey, Wein, Revenue Management of a Make-to-Stock Queue, Oper. Res. 54(5), 2006, p. 867, Proposition 2 ("K_Ω is a positive constant such that π_Ω integrates to one in Ω"); region (34), p. 866

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_expDensity
import Definitions.Def_MakeToStockRM_ExpDensity_region

namespace MakeToStockRM.ExpDensity

theorem normalizing_constant_exists (θ σ δ ϱ ymin ymax : ℝ) (η ξ : ℝ → ℝ)
    (hy : ymin < ymax) (hη : Continuous η) (hξ : Continuous ξ)
    (hlt : ∀ y ∈ Set.Icc ymin ymax, η y < ξ y) :
    MeasureTheory.IntegrableOn (expDensity θ σ δ ϱ) (region η ξ ymin ymax) ∧
      ∃! K : ℝ, 0 < K ∧ ∫ z in region η ξ ymin ymax, K * expDensity θ σ δ ϱ z = 1 := by sorry

end MakeToStockRM.ExpDensity
