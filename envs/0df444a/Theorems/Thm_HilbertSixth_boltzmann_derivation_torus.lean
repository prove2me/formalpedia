-- Prove2me | Theorems.Thm_HilbertSixth_boltzmann_derivation_torus
-- name    : HilbertSixth.boltzmann_derivation_torus
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T04:15:51.31498+00:00
-- url     : https://prove2.me/theorems/6d6d69af-a74e-4a54-a610-c9f0f31f3dcd
-- title:
--   Theorem 1: long-time derivation of the Boltzmann equation on $\mathbb{T}^d$
-- statement:
--   **Theorem 1 of arXiv:2503.01800.** Fix $d\in\{2,3\}$ and $\beta > 0$. Let $(\alpha, A, t_{\mathrm{fin}})$ satisfy
--
--   $$\max(1,\alpha)\cdot\max(1,A)\cdot\max(1,t_{\mathrm{fin}}) \ll (\log|\log\varepsilon|)^{1/2},$$
--
--   let $n_0 \ge 0$ have integral $1$ on $\mathbb{T}^d\times\mathbb{R}^d$, and suppose the solution $n$ of the Boltzmann equation with collision rate $\alpha$ and data $n_0$ exists on $[0, t_{\mathrm{fin}}]$ with
--
--   $$\|e^{2\beta|v|^2}n(t)\|_{L^\infty} \le A \ \ (t \in [0,t_{\mathrm{fin}}]), \qquad \|e^{2\beta|v|^2}\nabla_x n_0\|_{L^\infty} \le A.$$
--
--   Consider the hard-sphere system of diameter $\varepsilon$ with random initial configuration given by the grand canonical ensemble under the Boltzmann-Grad scaling. Then, for $\varepsilon$ small enough, uniformly in $t\in[0,t_{\mathrm{fin}}]$ and in $s \le |\log\varepsilon|$, the correlation functions satisfy
--
--   $$\Big\| f_s(t,z_s) - \prod_{j=1}^{s} n(t,z_j)\cdot\mathbf{1}_{\mathcal{D}_s}(z_s)\Big\|_{L^1(\mathbb{T}^{ds}\times\mathbb{R}^{ds})} \le \varepsilon^{\theta},$$
--
--   where $\theta > 0$ depends only on $d$. This is the kinetic half of Hilbert's programme, valid for the entire lifespan of the Boltzmann solution.
-- source:
--   Deng--Hani--Ma, Hilbert's sixth problem: derivation of fluid equations via Boltzmann's kinetic theory, https://arxiv.org/abs/2503.01800, pp. 6-7, Theorem 1 (eq. 1.16-1.18)

import Definitions.Def_HilbertSixth_HardSphere
import Definitions.Def_HilbertSixth_Boltzmann

open MeasureTheory HilbertSixth

namespace HilbertSixth
theorem boltzmann_derivation_torus (d : ℕ) (hd : d = 2 ∨ d = 3) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ β : ℝ, 0 < β →
        ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧
          ∀ ε α A tfin : ℝ, 0 < ε → ε < ε₀ → 0 < α → 0 < A → 0 < tfin →
            max 1 α * (max 1 A * max 1 tfin) ≤ c * Real.sqrt (Real.log |Real.log ε|) →
            ∀ (n₀ : Vec d → Vec d → ℝ) (n : ℝ → Vec d → Vec d → ℝ),
              (∀ x v : Vec d, 0 ≤ n₀ x v) →
              PeriodicPos₂ n₀ →
              (∀ t : ℝ, PeriodicPos₂ (n t)) →
              (∫ z in phaseRegion (box d), n₀ z.1 z.2) = 1 →
              IsBoltzmannSolution d α tfin n₀ n →
              (∀ t ∈ Set.Icc (0 : ℝ) tfin, ∀ x v : Vec d,
                Real.exp (2 * β * ‖v‖ ^ 2) * |n t x v| ≤ A) →
              (∀ x v : Vec d,
                Real.exp (2 * β * ‖v‖ ^ 2) * ‖gradVec (fun y => n₀ y v) x‖ ≤ A) →
              ∀ Φ : ∀ N, HardSphereFlow d N ε torusDist,
                ∀ s : ℕ, (s : ℝ) ≤ |Real.log ε| →
                  ∀ t ∈ Set.Icc (0 : ℝ) tfin,
                    (∫ zs in region (box d) s,
                        |corrOfFlow d α ε torusDist (box d) n₀ Φ t s zs
                          - (∏ j, n t (zs j).1 (zs j).2) *
                              domainIndicator torusDist s ε zs|) ≤ ε ^ θ := by
  sorry

end HilbertSixth
