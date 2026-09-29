-- Prove2me | Theorems.Thm_HilbertSixth_navier_stokes_fourier_from_newton
-- name    : HilbertSixth.navier_stokes_fourier_from_newton
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T04:26:41.874983+00:00
-- url     : https://prove2.me/theorems/aa1c7031-a8fb-426d-8c08-4661759cbe15
-- title:
--   Theorem 2(1): incompressible Navier--Stokes--Fourier from Newton's laws
-- statement:
--   **Theorem 2(1) of arXiv:2503.01800 — the goal of this mission.** Let $d\in\{2,3\}$ and let $(u,\rho)$ be a smooth solution of the incompressible Navier-Stokes-Fourier system on $\mathbb{T}^d\times[0,T_{\mathrm{fin}}]$. Consider the hard-sphere system of diameter $\varepsilon$ with random initial configuration drawn from the grand canonical ensemble with $\alpha = \delta^{-1}$ and well-prepared one-particle profile (1.21), the parameters being subject to $\max(1,\delta^{-1})\max(1,\delta^{-1}T_{\mathrm{fin}}) \ll (\log|\log\varepsilon|)^{1/2}$. Then, uniformly for $t\in[0,\delta^{-1}T_{\mathrm{fin}}]$, the one-particle correlation function satisfies
--
--   $$\Big\|f_1(t,x,v) - \frac{e^{-|v|^2/2}}{(2\pi)^{d/2}}\Big[1 + \delta\Big(\tfrac{2+d-|v|^2}{2}\rho(\delta t,x) + v\cdot u(\delta t,x)\Big)\Big]\Big\|_{L^1_{x,v}} \lesssim \delta^{3/2},$$
--
--   and consequently, in $L^\infty_t L^1_x$,
--
--   $$\frac{1}{\delta}\int_{|v|\le\varepsilon^{-\kappa}} f_1(t,x,v)\,v\,\mathrm{d}v \longrightarrow u(\delta t, x), \qquad \frac{1}{\delta}\Big(\int_{|v|\le\varepsilon^{-\kappa}} f_1(t,x,v)\,\mathrm{d}v - 1\Big) \longrightarrow \rho(\delta t, x)$$
--
--   as $\varepsilon, \delta \to 0$. This is the full chain from Newton's laws to the incompressible Navier-Stokes-Fourier equations: the macroscopic velocity and density of a hard-sphere gas converge to the solution of the fluid system.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, pp. 8-9, Theorem 2 part (1) (eq. 1.24-1.27)

import Definitions.Def_HilbertSixth_HardSphere
import Definitions.Def_HilbertSixth_Fluid

open MeasureTheory HilbertSixth

namespace HilbertSixth
theorem navier_stokes_fourier_from_newton (d : ℕ) (hd : d = 2 ∨ d = 3) :
    ∃ μ₁ μ₂ κ c : ℝ, 0 < μ₁ ∧ 0 < μ₂ ∧ 0 < κ ∧ 0 < c ∧
      ∀ (Tfin : ℝ) (u : ℝ → Vec d → Vec d) (ρ p : ℝ → Vec d → ℝ)
          (gR : Vec d → Vec d → ℝ),
        0 < Tfin →
        SmoothPeriodicVector d u → SmoothPeriodicScalar d ρ →
        SmoothPeriodicScalar d p →
        IsNSFSolution d μ₁ μ₂ Tfin u ρ p →
        (∀ v : Vec d, PeriodicPos (fun x => gR x v)) →
        (∀ v : Vec d, (∫ x in box d, gR x v) = 0) →
        WeightedDerivBound d (4 * d) (fun _ v => jbracket v ^ (2 * d)) gR →
        ∃ C δ₀ ε₀ : ℝ, 0 < C ∧ 0 < δ₀ ∧ 0 < ε₀ ∧
          -- (1.26): the one-particle correlation function is, in `L¹(T^d × ℝ^d)`,
          -- the local Maxwellian fluctuation profile of the fluid solution up to
          -- an error `O(δ^{3/2})`
          (∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ →
              max 1 δ⁻¹ * max 1 (δ⁻¹ * Tfin) ≤ c * Real.sqrt (Real.log |Real.log ε|) →
              (∀ x v : Vec d, 0 ≤ nsfInitialData d δ (ρ 0) (u 0) gR x v) →
              ∀ Φ : ∀ N, HardSphereFlow d N ε torusDist,
                ∀ t ∈ Set.Icc (0 : ℝ) (δ⁻¹ * Tfin),
                  (∫ z in phaseRegion (box d),
                      |oneCorr d δ⁻¹ ε torusDist (box d)
                          (nsfInitialData d δ (ρ 0) (u 0) gR) Φ t z.1 z.2
                        - nsfProfile d δ (ρ (δ * t)) (u (δ * t)) z.1 z.2|)
                    ≤ C * δ ^ ((3 : ℝ) / 2)) ∧
          -- (1.27): the rescaled truncated moments of the particle system converge,
          -- in `L^∞_t L¹_x`, to the fluid velocity and density
          (∀ η : ℝ, 0 < η → ∃ ε₁ δ₁ : ℝ, 0 < ε₁ ∧ 0 < δ₁ ∧
            ∀ ε δ : ℝ, 0 < ε → ε < min ε₀ ε₁ → 0 < δ → δ < min δ₀ δ₁ →
              max 1 δ⁻¹ * max 1 (δ⁻¹ * Tfin) ≤ c * Real.sqrt (Real.log |Real.log ε|) →
              (∀ x v : Vec d, 0 ≤ nsfInitialData d δ (ρ 0) (u 0) gR x v) →
              ∀ Φ : ∀ N, HardSphereFlow d N ε torusDist,
                ∀ t ∈ Set.Icc (0 : ℝ) (δ⁻¹ * Tfin),
                  (∫ x in box d,
                      ‖δ⁻¹ • (∫ v in Metric.closedBall (0 : Vec d) (ε ^ (-κ)),
                            oneCorr d δ⁻¹ ε torusDist (box d)
                              (nsfInitialData d δ (ρ 0) (u 0) gR) Φ t x v • v)
                        - u (δ * t) x‖) ≤ η ∧
                  (∫ x in box d,
                      |δ⁻¹ * ((∫ v in Metric.closedBall (0 : Vec d) (ε ^ (-κ)),
                            oneCorr d δ⁻¹ ε torusDist (box d)
                              (nsfInitialData d δ (ρ 0) (u 0) gR) Φ t x v) - 1)
                        - ρ (δ * t) x|) ≤ η) := by
  sorry

end HilbertSixth
