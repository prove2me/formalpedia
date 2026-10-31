-- Prove2me | Theorems.Thm_KellyStochasticNetworks_LossLimits_fluctuation_charFun_limit
-- name    : KellyStochasticNetworks.LossLimits.fluctuation_charFun_limit
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T05:11:07.261502+00:00
-- url     : https://prove2.me/theorems/afd9c57c-89ff-474d-9576-877feea5c437
-- title:
--   Theorem 3.14 (limit identification) — characteristic functions of $u(N)$ converge
-- statement:
--   **Setting (limiting regime of §3.5.1).** Fix a matrix $A\in\mathbb N^{J\times R}$ of full row rank. For $N\ge 1$ let $\nu_r(N)>0$ and let $C_j(N)$ be positive integers with $\nu_r(N)/N\to\nu_r>0$ and $C_j(N)/N\to C_j>0$. Let $B$ solve the blocking conditions (3.6) for $(\nu,C)$, put $x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$, and assume strict slack $(Ax)_j<C_j$ whenever $B_j=0$. Let $n(N)$ have the exact law (3.3) for the data $(\nu(N),C(N))$ and $u(N)=(n(N)-x(N))/\sqrt N$, where $x(N)$ is the mode for $(\nu(N),C(N))$.
--
--   Write $\mathcal B=\{j:B_j>0\}$, $H=A_{\mathcal B}$, $D=\operatorname{diag}(x)$, and let $U=Z-DH^{\mathsf T}(HDH^{\mathsf T})^{-1}HZ$ with $Z_r\sim\mathcal N(0,x_r)$ independent: the normal vector conditioned on $HU=0$.
--
--   **Claim (convergence of characteristic functions).** For every $\xi\in\mathbb R^R$,
--   $$\mathbb E\,e^{i\,\xi\cdot u(N)}\longrightarrow \mathbb E\,e^{i\,\xi\cdot U}\qquad(N\to\infty).$$
--
--   By Lévy's continuity theorem this is equivalent to the distributional convergence $u(N)\Rightarrow U$ asserted in Theorem 3.14; it is the identification of the limit carried out in the sketch of proof (the Stirling expansion and the conditioning effect of the geometric factor $\prod_j(1-B_j(N))^{m_j(N)}$).
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF (statslab.cam.ac.uk/~frank/STOCHNET/LNSN/book.pdf), §3.5.2, printed pp. 64–66 (PDF pp. 72–74): Theorem 3.14 and Remark 3.16 (tightness/tail control of u(N)); DOI 10.1017/cbo9781139565363.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws
import Definitions.Def_KellyStochasticNetworks_LossLimits_Gaussian

open MeasureTheory Filter Topology

namespace KellyStochasticNetworks.LossLimits

/-- Convergence of characteristic functions in Theorem 3.14: in the limiting regime of
§3.5.1 (full row rank, ν(N)/N → ν > 0, C(N)/N → C > 0, strict slack), for every
ξ ∈ ℝ^R the characteristic function E exp(i ξ·u(N)) of the exact fluctuation law of
u(N) = (n(N) - x(N))/sqrt N converges to that of the conditioned Gaussian law
(independent N(0, x_r) coordinates conditioned on A_B u = 0, realised as the
regression residual z - D A_Bᵀ (A_B D A_Bᵀ)⁻¹ A_B z). -/
theorem fluctuation_charFun_limit {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) (ξ : Fin R → ℝ) :
    Tendsto (fun N => ∫ u, Complex.exp (Complex.I * ∑ r, (ξ r : ℂ) * (u r : ℂ))
        ∂(fluctuationLaw A νN CN N)) atTop
      (𝓝 (∫ u, Complex.exp (Complex.I * ∑ r, (ξ r : ℂ) * (u r : ℂ))
        ∂(conditionedGaussian A (blocking A ν C) (mode A ν C)))) := by sorry

end KellyStochasticNetworks.LossLimits
