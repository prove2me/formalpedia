-- Prove2me | Theorems.Thm_HilbertSixth_boltzmann_derivation_euclidean
-- name    : HilbertSixth.boltzmann_derivation_euclidean
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-20T04:33:37.665704+00:00
-- url     : https://prove2.me/theorems/1d53db5d-150f-44d7-8dfc-700408a89edb
-- title:
--   Theorem 1 of arXiv:2408.07818: long-time derivation of the Boltzmann equation on $\mathbb{R}^d$
-- statement:
--   **Theorem 1 of arXiv:2408.07818**, the companion whole-space result. Fix $d \ge 2$, $\beta > 0$, and a nonnegative $f_0$ of integral $1$ on $\mathbb{R}^d\times\mathbb{R}^d$. Suppose the solution $f$ of the Boltzmann equation (collision rate $1$) exists on $[0,t_{\mathrm{fin}}]$ with $\|e^{2\beta|v|^2}f(t)\|_{L^\infty}\le A$, and that $\|f_0\|_{\mathrm{Bol}_{2\beta}} + \|\nabla_x f_0\|_{\mathrm{Bol}_{2\beta}} \le B_0$, where $\|g\|_{\mathrm{Bol}_\beta} = \sum_{k\in\mathbb{Z}^d}\sup_{|x-k|\le 1,v}e^{\beta|v|^2}|g(x,v)|$.
--
--   Consider the hard-sphere system of diameter $\varepsilon$ on $\mathbb{R}^d$ with random initial data given by the grand canonical ensemble under the Boltzmann-Grad scaling $N\varepsilon^{d-1}\approx 1$. Then, for $\varepsilon$ small enough depending on $(d, t_{\mathrm{fin}},\beta, A, B_0)$, uniformly in $t\in[0,t_{\mathrm{fin}}]$ and in $s\le|\log\varepsilon|$,
--
--   $$\Big\|f_s(t,z_s) - \prod_{j=1}^{s} f(t,z_j)\cdot\mathbf{1}_{\mathcal{D}_s}(z_s)\Big\|_{L^1(\mathbb{R}^{2ds})} \le \varepsilon^{\theta}$$
--
--   with $\theta>0$ depending only on $d$. Note $t_{\mathrm{fin}}$ may be arbitrarily large: the derivation is valid for the entire lifespan of the kinetic solution.
-- source:
--   Deng--Hani--Ma, Long time derivation of the Boltzmann equation from hard sphere dynamics, https://arxiv.org/abs/2408.07818, p. 6, Theorem 1 (eq. 1.15-1.18)

import Definitions.Def_HilbertSixth_HardSphere
import Definitions.Def_HilbertSixth_Boltzmann

open MeasureTheory HilbertSixth

namespace HilbertSixth
theorem boltzmann_derivation_euclidean (d : ℕ) (hd : 2 ≤ d) :
    ∃ θ : ℝ, 0 < θ ∧
      ∀ β A B₀ tfin : ℝ, 0 < β → 0 < A → 0 < B₀ → 0 < tfin →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧
          ∀ ε : ℝ, 0 < ε → ε < ε₀ →
            ∀ (f₀ : Vec d → Vec d → ℝ) (f : ℝ → Vec d → Vec d → ℝ),
              (∀ x v : Vec d, 0 ≤ f₀ x v) →
              (∫ z : Phase d, f₀ z.1 z.2) = 1 →
              IsBoltzmannSolution d 1 tfin f₀ f →
              (∀ t ∈ Set.Icc (0 : ℝ) tfin, ∀ x v : Vec d,
                Real.exp (2 * β * ‖v‖ ^ 2) * |f t x v| ≤ A) →
              BolLe d (2 * β) B₀ f₀ →
              BolLe d (2 * β) B₀ (fun x v => ‖gradVec (fun y => f₀ y v) x‖) →
              ∀ Φ : ∀ N, HardSphereFlow d N ε euclSep,
                ∀ s : ℕ, (s : ℝ) ≤ |Real.log ε| →
                  ∀ t ∈ Set.Icc (0 : ℝ) tfin,
                    (∫ zs : Config d s,
                        |corrOfFlow d 1 ε euclSep Set.univ f₀ Φ t s zs
                          - (∏ j, f t (zs j).1 (zs j).2) *
                              domainIndicator euclSep s ε zs|) ≤ ε ^ θ := by
  sorry

end HilbertSixth
