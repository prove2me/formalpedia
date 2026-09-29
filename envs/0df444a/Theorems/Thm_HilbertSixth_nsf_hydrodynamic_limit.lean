-- Prove2me | Theorems.Thm_HilbertSixth_nsf_hydrodynamic_limit
-- name    : HilbertSixth.nsf_hydrodynamic_limit
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T04:25:59.427261+00:00
-- url     : https://prove2.me/theorems/c034abb7-f85f-47ff-9f1f-b3069b8b24aa
-- title:
--   Proposition 1.6: incompressible Navier--Stokes--Fourier limit of the Boltzmann equation
-- statement:
--   **Proposition 1.6 of arXiv:2503.01800**, quoted from Gallagher-Tristani. Let $d \in \{2,3\}$. There are positive constants $\mu_1, \mu_2$ (depending only on $d$) such that the following holds for the incompressible Navier-Stokes-Fourier system
--
--   $$\partial_t u + (u\cdot\nabla)u - \mu_1\Delta u = -\nabla p, \qquad \partial_t\rho + (u\cdot\nabla)\rho - \mu_2\Delta\rho = 0, \qquad \operatorname{div}u = 0$$
--
--   on $\mathbb{T}^d$. Fix a smooth zero-mean solution $(u,\rho)$ on $[0, T_{\mathrm{fin}}]$ and a perturbation $g_R$ with zero mean in $x$ and bounded weighted derivatives. Then for all sufficiently small $\delta > 0$, the Boltzmann equation with $\alpha = \delta^{-1}$ and well-prepared data (1.21) has a solution on $[0, \delta^{-1}T_{\mathrm{fin}}]$ of the form
--
--   $$n(t,x,v) = \frac{e^{-|v|^2/2}}{(2\pi)^{d/2}}\Big[1 + \delta\Big(\tfrac{2+d-|v|^2}{2}\rho(\delta t,x) + v\cdot u(\delta t, x)\Big)\Big] + h(\delta t, x, v),$$
--
--   with $\|e^{|v|^2/4}h(\tau)\|_{L^\infty} + \|e^{|v|^2/4}\nabla_x h(\tau)\|_{L^\infty} \lesssim \delta^{3/2}$ uniformly in $\tau\in[0,T_{\mathrm{fin}}]$.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, pp. 7-8, Proposition 1.6 (eq. 1.19-1.23); after Gallagher--Tristani, arXiv:1905.02463

import Definitions.Def_HilbertSixth_Fluid

open MeasureTheory HilbertSixth

namespace HilbertSixth
theorem nsf_hydrodynamic_limit (d : ℕ) (hd : d = 2 ∨ d = 3) :
    ∃ μ₁ μ₂ : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧
      ∀ (Tfin : ℝ) (u : ℝ → Vec d → Vec d) (ρ p : ℝ → Vec d → ℝ)
          (gR : Vec d → Vec d → ℝ),
        0 < Tfin →
        SmoothPeriodicVector d u → SmoothPeriodicScalar d ρ →
        SmoothPeriodicScalar d p →
        IsNSFSolution d μ₁ μ₂ Tfin u ρ p →
        (∀ v : Vec d, PeriodicPos (fun x => gR x v)) →
        (∀ v : Vec d, (∫ x in box d, gR x v) = 0) →
        WeightedDerivBound d (4 * d) (fun _ v => jbracket v ^ (2 * d)) gR →
        ∃ C δ₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧
          ∀ δ : ℝ, 0 < δ → δ < δ₀ →
            (∀ x v : Vec d, 0 ≤ nsfInitialData d δ (ρ 0) (u 0) gR x v) →
            ∃ n h : ℝ → Vec d → Vec d → ℝ,
              IsBoltzmannSolution d δ⁻¹ (δ⁻¹ * Tfin)
                  (nsfInitialData d δ (ρ 0) (u 0) gR) n ∧
              (∀ t ∈ Set.Icc (0 : ℝ) (δ⁻¹ * Tfin), ∀ x v : Vec d,
                n t x v = nsfProfile d δ (ρ (δ * t)) (u (δ * t)) x v + h (δ * t) x v) ∧
              (∀ τ ∈ Set.Icc (0 : ℝ) Tfin, ∀ x v : Vec d,
                Real.exp (‖v‖ ^ 2 / 4) * |h τ x v| ≤ C * δ ^ ((3 : ℝ) / 2)) ∧
              (∀ τ ∈ Set.Icc (0 : ℝ) Tfin, ∀ x v : Vec d,
                Real.exp (‖v‖ ^ 2 / 4) * ‖gradVec (fun y => h τ y v) x‖
                  ≤ C * δ ^ ((3 : ℝ) / 2)) := by
  sorry

end HilbertSixth
