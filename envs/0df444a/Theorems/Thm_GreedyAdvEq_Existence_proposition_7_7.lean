-- Prove2me | Theorems.Thm_GreedyAdvEq_Existence_proposition_7_7
-- name    : GreedyAdvEq.Existence.proposition_7_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:11.434106+00:00
-- url     : https://prove2.me/theorems/97da17d0-9683-41cc-ab55-93952e676c5a
-- title:
--   Proposition 7.7, p. 31, (55)–(56) — the zeroth-order estimator Γ̂ has mean ∇ₓ𝔥 and a Gaussian tail 2exp(−t²/(8(2b√d/σ)²))
-- statement:
--   Let $d\ge1$, let $f$ be $C^2$ and $b$-bounded with $L$-Lipschitz Hessian, and let $h_{\varepsilon^\circ}$ be built from Algorithm 1 with an admissible eigen-oracle and hyperparameters $\delta,\mu_1,\mu_3>0$, $\mu_4\ge0$. Let $\sigma,\varepsilon^\circ>0$, $x,y,\hat x\in\mathbb R^d$, and let $c$ be a constant with $c\ge0$ and $|c|\le b$. For $u\sim N(0,I_d)$ define
--   $$\hat\Gamma^{\hat x}_{\varepsilon^\circ}(x,y)=\big[\mathbb h^{\hat x}_{\varepsilon^\circ}(x+\sigma u,y)-c\big]\frac1\sigma u.$$
--   Assume that $u\mapsto\mathbb h^{\hat x}_{\varepsilon^\circ}(x'+\sigma u,y)$ is integrable under $N(0,I_d)$ for every $x'$. Then $\mathfrak h^{\hat x}_{\varepsilon^\circ,\sigma}(\cdot,y)$ is differentiable at $x$ with
--   $$\mathbb E\big[\hat\Gamma^{\hat x}_{\varepsilon^\circ}(x,y)\big]=\nabla_x\mathfrak h^{\hat x}_{\varepsilon^\circ,\sigma}(x,y), \tag{55}$$
--   and for every $t\ge0$,
--   $$\mathbb P\Big(\big\|\hat\Gamma^{\hat x}_{\varepsilon^\circ}(x,y)-\nabla_x\mathfrak h^{\hat x}_{\varepsilon^\circ,\sigma}(x,y)\big\|\ge t\Big)\le2\exp\Big(-\frac{t^2}{8\,(2b\sqrt d/\sigma)^2}\Big). \tag{56}$$
--
--   The estimator uses only function values of the computable $h$, so it is the gradient oracle of the noisy zeroth-order descent in Algorithm 2.
--
--   **Formalization Note.** The integrability hypothesis is added: $h$ depends on the eigen-oracle, which need not be measurable, and without it both sides of (55) would be Lean's junk value $0$. Differentiability in (55) is asserted (`HasGradientAt`), not read off `gradient`. $\mathbb P$ is the standard Gaussian measure on $\mathbb R^d$.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 31, Proposition 7.7, (55)–(56)

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting
import Definitions.Def_GreedyAdvEq_Existence_Algorithm1

namespace GreedyAdvEq.Existence

open MeasureTheory ProbabilityTheory

theorem proposition_7_7 (d : ℕ) (hd : 0 < d) (f : E d → E d → ℝ) (b L : ℝ) (hb : 0 < b)
    (hL : 0 < L) (hf : IsModel f b L) (Eig : E d → E d → ℝ × E d) (δ μ₁ μ₃ μ₄ : ℝ)
    (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₃ : 0 < μ₃) (hμ₄ : 0 ≤ μ₄) (hEig : IsEigOracle f Eig μ₄)
    (σ : ℝ) (hσ : 0 < σ) (ε : ℝ) (hε : 0 < ε) (x y xh : E d) (c : ℝ) (hc : 0 ≤ c)
    (hcb : |c| ≤ b)
    (hint : ∀ x' : E d, Integrable (fun u : E d => hTrunc f L Eig δ μ₁ μ₃ ε xh (x' + σ • u) y)
      (stdGaussian (E d))) :
    HasGradientAt (fun x' => hSmooth f L Eig δ μ₁ μ₃ ε σ xh x' y)
        (∫ u, ((hTrunc f L Eig δ μ₁ μ₃ ε xh (x + σ • u) y - c) * (1 / σ)) • u
          ∂(stdGaussian (E d))) x ∧
      ∀ t : ℝ, 0 ≤ t →
        (stdGaussian (E d)).real
            {u : E d | t ≤ ‖((hTrunc f L Eig δ μ₁ μ₃ ε xh (x + σ • u) y - c) * (1 / σ)) • u -
              gradient (fun x' => hSmooth f L Eig δ μ₁ μ₃ ε σ xh x' y) x‖} ≤
          2 * Real.exp (-(t ^ 2 / (8 * (2 * b * Real.sqrt d / σ) ^ 2))) := by sorry

end GreedyAdvEq.Existence
