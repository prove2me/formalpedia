-- Prove2me | Theorems.Thm_HilbertSixth_compressible_euler_from_newton
-- name    : HilbertSixth.compressible_euler_from_newton
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T04:29:09.12412+00:00
-- url     : https://prove2.me/theorems/1b4cad90-da4a-4aaf-b226-996fbc52c996
-- title:
--   Theorem 3(1): compressible Euler from Newton's laws, given the Hilbert expansion
-- statement:
--   **Theorem 3(1) of arXiv:2503.01800**, in the conditional form in which the paper proves it (Theorem 1 combined with Proposition 1.8). Let $d\in\{2,3\}$ and let $(\rho, u, \Theta, p)$ be a smooth solution of the compressible Euler system on $\mathbb{T}^d\times[0,T_{\mathrm{fin}}]$ with positive density and temperature, and let $\mathcal{M}$ be the associated local Maxwellian (1.41).
--
--   Assume the Hilbert expansion input of Proposition 1.8: functions $F_0,\dots,F_6$ with $F_0 = \mathcal{M}$, a perturbation $F_R$ with the weighted derivative bound (1.44), initial data $n_0 = \sum_{j\le 6}\delta^j F_j(0) + \delta^3 F_R \ge 0$ of integral $1$, and a solution $n$ of the Boltzmann equation with $\alpha = \delta^{-1}$ satisfying $n = \sum_{j\le 6}\delta^j F_j + h$ with $\|\mathcal{M}^{-1/2}h\|_{L^\infty} + \|\mathcal{M}^{-1/2}\nabla_x h\|_{L^\infty} \lesssim \delta^{3/2}$.
--
--   Then, for the hard-sphere system with the corresponding grand canonical data and parameters as in Theorem 2, uniformly in $t\in[0,T_{\mathrm{fin}}]$,
--
--   $$\Big\| f_1(t,x,v) - \frac{\rho(t,x)}{(2\pi \Theta(t,x))^{d/2}}e^{-|v-u(t,x)|^2/(2\Theta(t,x))}\Big\|_{L^1_{x,v}} \lesssim \delta .$$
--
--   Only estimate (1.47) is formalized here. The three limits (1.48) of the source are deliberately omitted: as printed they identify $\lim\int f_1 v\,\mathrm{d}v$ with $u$ and $\lim\int f_1(|v|^2-d)/d\,\mathrm{d}v$ with $\Theta$, whereas the moments of the local Maxwellian are $\rho u$ and $\rho(\Theta + |u|^2/d - 1)$, so those two identities require a normalisation that the source does not state.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, pp. 10-11, Theorem 3 part (1), eq. (1.47), with the input of Proposition 1.8 (eq. 1.41-1.46)

import Definitions.Def_HilbertSixth_HardSphere
import Definitions.Def_HilbertSixth_Fluid

open MeasureTheory HilbertSixth

namespace HilbertSixth
theorem compressible_euler_from_newton (d : ℕ) (hd : d = 2 ∨ d = 3) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Tfin : ℝ) (ρ Θ p : ℝ → Vec d → ℝ) (u : ℝ → Vec d → Vec d)
          (F : ℕ → ℝ → Vec d → Vec d → ℝ) (FR : Vec d → Vec d → ℝ) (C₁ : ℝ),
        0 < Tfin → 0 < C₁ →
        SmoothPeriodicScalar d ρ → SmoothPeriodicScalar d Θ →
        SmoothPeriodicScalar d p → SmoothPeriodicVector d u →
        IsCompressibleEulerSolution d Tfin ρ Θ p u →
        (∀ (t : ℝ) (x v : Vec d),
          F 0 t x v = localMaxwellian d (ρ t) (Θ t) (u t) x v) →
        (∀ (j : ℕ) (t : ℝ), PeriodicPos₂ (F j t)) →
        (∀ v : Vec d, PeriodicPos (fun x => FR x v)) →
        WeightedDerivBound d (4 * d)
            (fun x v => localMaxwellian d (ρ 0) (Θ 0) (u 0) x v ^ (-(1 : ℝ) / 2) *
              jbracket v ^ (2 * d)) FR →
        ∃ C₂ δ₀ ε₀ : ℝ, 0 < C₂ ∧ 0 < δ₀ ∧ 0 < ε₀ ∧
          ∀ ε δ : ℝ, 0 < ε → ε < ε₀ → 0 < δ → δ < δ₀ →
            max 1 δ⁻¹ * max 1 (δ⁻¹ * Tfin) ≤ c * Real.sqrt (Real.log |Real.log ε|) →
            ∀ n₀ : Vec d → Vec d → ℝ,
              (∀ x v : Vec d,
                n₀ x v = (∑ j ∈ Finset.range 7, δ ^ j * F j 0 x v) + δ ^ 3 * FR x v) →
              (∀ x v : Vec d, 0 ≤ n₀ x v) →
              (∫ z in phaseRegion (box d), n₀ z.1 z.2) = 1 →
              ∀ n h : ℝ → Vec d → Vec d → ℝ,
                IsBoltzmannSolution d δ⁻¹ Tfin n₀ n →
                (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x v : Vec d,
                  n t x v = (∑ j ∈ Finset.range 7, δ ^ j * F j t x v) + h t x v) →
                (∀ t ∈ Set.Icc (0 : ℝ) Tfin, ∀ x v : Vec d,
                  localMaxwellian d (ρ t) (Θ t) (u t) x v ^ (-(1 : ℝ) / 2) *
                      (|h t x v| + ‖gradVec (fun y => h t y v) x‖)
                    ≤ C₁ * δ ^ ((3 : ℝ) / 2)) →
                ∀ Φ : ∀ N, HardSphereFlow d N ε torusDist,
                  ∀ t ∈ Set.Icc (0 : ℝ) Tfin,
                    (∫ z in phaseRegion (box d),
                        |oneCorr d δ⁻¹ ε torusDist (box d) n₀ Φ t z.1 z.2
                          - localMaxwellian d (ρ t) (Θ t) (u t) z.1 z.2|) ≤ C₂ * δ := by
  sorry

end HilbertSixth
