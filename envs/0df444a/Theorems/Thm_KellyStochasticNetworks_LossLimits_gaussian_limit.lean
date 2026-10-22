-- Prove2me | Theorems.Thm_KellyStochasticNetworks_LossLimits_gaussian_limit
-- name    : KellyStochasticNetworks.LossLimits.gaussian_limit
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:44.84224+00:00
-- url     : https://prove2.me/theorems/5df7e5c9-213e-4bd0-aa17-965978be164b
-- title:
--   Theorem 3.14 — Gaussian limit and convergence of moments
-- statement:
--   Fix a natural matrix $A\in\mathbb N^{J\times R}$ of full row rank. For $N\ge1$, let $\nu_r(N)>0$ and let $C_j(N)$ be positive integers, with $\nu_r(N)/N\to\nu_r>0$ and $C_j(N)/N\to C_j>0$. Let $B(N)$ and $B$ solve the corresponding blocking conditions (3.6), and set $x_r(N)=\nu_r(N)\prod_j(1-B_j(N))^{A_{jr}}$ and $x_r=\nu_r\prod_j(1-B_j)^{A_{jr}}$. Assume strict slack $(Ax)_j<C_j$ at every link with $B_j=0$.
--
--   Let $n(N)$ have the exact stationary product-form law (3.3), proportional to $\prod_r\nu_r(N)^{n_r}/n_r!$ on $An\le C(N)$. Put $u(N)=(n(N)-x(N))/\sqrt N$. Write $\mathcal B=\{j:B_j>0\}$, $H=A_{\mathcal B}$ and $D=\operatorname{diag}(x)$. If $Z_r\sim\mathcal N(0,x_r)$ independently, let $U=Z-DH^{\mathsf T}(HDH^{\mathsf T})^{-1}HZ$. Then
--   $$u(N)\Rightarrow U,\qquad \mathbb E\!\left[\prod_r u_r(N)^{k_r}\right]\longrightarrow\mathbb E\!\left[\prod_r U_r^{k_r}\right]\quad(k\in\mathbb N^R),$$
--   and
--   $$\frac{\mathbb E[n_r(N)]}{N}\longrightarrow x_r\quad(r\in\mathcal R).$$
--   All displayed moments are integrable. The law of $U$ is the canonical law of independent normals with variances $x_r$ conditioned on $HU=0$.
--
--   The theorem describes the stationary fluctuations of a large fixed-topology loss network, including the possible loss of dimension caused by active capacity constraints.
--
--   **Formalization Note** Weak convergence is stated against all bounded continuous real test functions. The centering is exactly $x(N)$, never $Nx$. Conditioning on the null event uses the explicit Gaussian regression residual with covariance $D-DH^{\mathsf T}(HDH^{\mathsf T})^{-1}HD$. All mixed moments, their integrability, and the mean-occupancy consequence are retained. Tightness and tail control are proof obligations, not hypotheses.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 64 (PDF p. 72), Theorem 3.14; DOI 10.1017/cbo9781139565363.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws
import Definitions.Def_KellyStochasticNetworks_LossLimits_Gaussian

open MeasureTheory Filter Topology

namespace KellyStochasticNetworks.LossLimits

/-- Theorem 3.14. Definitions used below:
* Scaling: A has full row rank; ν(N)>0 and natural C(N)>0 for N≥1;
  ν(N)/N→ν>0 and C(N)/N→C>0, coordinatewise.
* blocking A ν C: the selected solution of (3.6), 0≤B<1, Ax≤C,
  with equality on B_j>0; x_r=ν_r∏_j(1-B_j)^A_jr is `mode`.
* strictSlack: (Ax)_j<C_j at every link with B_j=0.
* occupancyLaw: on n∈ℕ^R, mass proportional to ∏_r ν_r^n_r/n_r!,
  supported on An≤C, with the exact partition sum, not an assumed normalizer.
* fluctuationLaw: the image of that law under (n-x(N))/sqrt(N).
* conditionedGaussian: if D=diag(x), H=A restricted to B_j>0,
  the image of independent N(0,x_r) coordinates under
  z↦z-D Hᵀ(H D Hᵀ)⁻¹Hz. Its covariance is D-DHᵀ(HDHᵀ)⁻¹HD.
* monomial k u = ∏_r (u_r)^(k_r).
The first clause is weak convergence against all bounded continuous real functions;
the next clauses give existence and convergence of all mixed moments, and the final
clause is the printed convergence of mean occupancy divided by N. -/
theorem gaussian_limit {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (νN : ℕ → Fin R → ℝ) (CN : ℕ → Fin J → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℝ)
    (hscale : Scaling A νN CN ν C) (hslack : strictSlack A ν C) :
    let γ := conditionedGaussian A (blocking A ν C) (mode A ν C)
    (∀ f : (Fin R → ℝ) → ℝ, Continuous f → Bornology.IsBounded (Set.range f) →
      Tendsto (fun N => ∫ u, f u ∂(fluctuationLaw A νN CN N))
        atTop (𝓝 (∫ u, f u ∂γ))) ∧
    (∀ k : Fin R → ℕ,
      (∀ N, 0 < N → Integrable (monomial k) (fluctuationLaw A νN CN N)) ∧
      Integrable (monomial k) γ ∧
      Tendsto (fun N => ∫ u, monomial k u ∂(fluctuationLaw A νN CN N))
        atTop (𝓝 (∫ u, monomial k u ∂γ))) ∧
    (∀ r, (∀ N, 0 < N → Integrable (fun n : Fin R → ℕ => (n r : ℝ))
        (occupancyLaw A (νN N) (CN N))) ∧
      Tendsto (fun N => (∫ n, (n r : ℝ) ∂(occupancyLaw A (νN N) (CN N))) / N)
        atTop (𝓝 (mode A ν C r))) := by sorry

end KellyStochasticNetworks.LossLimits
