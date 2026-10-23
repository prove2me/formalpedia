-- Prove2me | Theorems.Thm_GreedyAdvEq_Existence_lemma_7_3
-- name    : GreedyAdvEq.Existence.lemma_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:33:25.630201+00:00
-- url     : https://prove2.me/theorems/6d5cdd68-16f3-42ae-b269-ada7e498f38e
-- title:
--   Lemma 7.3, p. 26 — (32)–(36) for h_ε at (x⋆, y⋆) make x⋆ an (ε, σ)-approximate local minimum of g_ε(·, y⋆) (read with σ, ε ≤ 1 and b ≥ 1)
-- statement:
--   Let $d\ge1$, let $f$ be $C^2$ and $b$-bounded with $L$-Lipschitz Hessian, $b\ge1$, and let $h_\varepsilon$ be built from Algorithm 1 with an admissible eigen-oracle and hyperparameters $\delta,\mu_1,\mu_3>0$, $\mu_4\ge0$. Let $0<\varepsilon\le1$ and $0<\sigma\le1$ with $\sigma\le1/\sqrt{\varepsilon d}$, and let $(x^\star,y^\star)\in\mathbb R^d\times\mathbb R^d$. Assume the truncated functions $\mathbb h^{x^\star}_\varepsilon(\cdot,y^\star)$ and $\mathbb g^{x^\star}_\varepsilon(\cdot,y^\star)$ are integrable along every Gaussian shift $x+\sigma\zeta$, and that
--   $$h_\varepsilon(x,y)\le g_\varepsilon(x,y)\quad\forall x,y\in\mathbb R^d\quad\text{(lower bound)}, \tag{32}$$
--   $$h_\varepsilon(x^\star,y^\star)=g_\varepsilon(x^\star,y^\star)\quad\text{(fixed-point property)}, \tag{33}$$
--   $$\mathbb E\big[\|\mathcal H^{x^\star}_\varepsilon(x^\star,y^\star)\|\big]\le\frac1{8000}\,\frac{\sigma^{14}\varepsilon^{1.5}}{b^2}\quad\text{(low SG)}, \tag{34}$$
--   and that $\mathfrak h^{x^\star}_{\varepsilon,\sigma}(\cdot,y^\star)$ is twice differentiable at $x^\star$ with
--   $$\|\nabla_x\mathfrak h^{x^\star}_{\varepsilon,\sigma}(x^\star,y^\star)\|\le\frac{\varepsilon^2\sigma^7}{8000\,b},\qquad\lambda_{\min}\big(\nabla_x^2\mathfrak h^{x^\star}_{\varepsilon,\sigma}(x^\star,y^\star)\big)\ge-\frac{\sqrt\varepsilon}5. \tag{35–36}$$
--   Then $x^\star$ is an $(\varepsilon,\sigma)$-approximate local minimum of $g_\varepsilon(\cdot,y^\star)$ (Definition 2.3): $\mathfrak g^{x^\star}_{\varepsilon,\sigma}(\cdot,y^\star)$ is twice differentiable at $x^\star$ with
--   $$\|\nabla_x\mathfrak g^{x^\star}_{\varepsilon,\sigma}(x^\star,y^\star)\|\le\varepsilon\quad\text{and}\quad\lambda_{\min}\big(\nabla_x^2\mathfrak g^{x^\star}_{\varepsilon,\sigma}(x^\star,y^\star)\big)\ge-\sqrt\varepsilon. \tag{37–38}$$
--
--   This is the analytic heart of the existence proof: approximate local minimality of the computable, smoothed lower bound $h$ transfers to the smoothed greedy max $g$, which is condition (7) of a greedy adversarial equilibrium.
--
--   **Formalization Note.** The page states the lemma for every $\varepsilon>0$ and $\sigma\le1/\sqrt{\varepsilon d}$; its proof (p. 28) concludes (37) "because $\sigma\le1/\sqrt{\varepsilon d}$, $b\ge1$, and $\sigma,\varepsilon\le1$", and (42) uses $\sigma\le1$. Without $\sigma\le1$ the printed lemma fails: for $f(x,y)=\phi(x)$ one has $h=g=\phi$, and with $d=b=1$, $\sigma=10$, $\varepsilon=1/100$ a bounded decreasing $\phi$ with a sharp step gives $\|\nabla\mathfrak h\|\approx0.04$, within the bound $0.125$ of (35) but above $\varepsilon$. The hypotheses $\sigma\le1$, $\varepsilon\le1$ and $b\ge1$ ($b\ge1$ is §7.1's "without loss of generality") are therefore added. Integrability of the two truncations is added so that the expectations in (34)–(38) are genuine. Derivatives are asserted (Fréchet derivatives near and at $x^\star$) before they are bounded; norms of derivatives are operator norms, equal to gradient norms; $\lambda_{\min}$ bounds are quadratic-form bounds.
-- source:
--   Mangoubi, Vishnoi, Greedy Adversarial Equilibrium, arXiv:2006.12363v4, p. 26, Lemma 7.3, (32)–(38); proof pp. 27–29 (σ, ε ≤ 1 and b ≥ 1 used on p. 28)

import Mathlib
import Definitions.Def_GreedyAdvEq_Existence_Setting
import Definitions.Def_GreedyAdvEq_Existence_Algorithm1

namespace GreedyAdvEq.Existence

open MeasureTheory ProbabilityTheory Filter Topology

theorem lemma_7_3 (d : ℕ) (hd : 0 < d) (f : E d → E d → ℝ) (b L : ℝ) (hb : 1 ≤ b)
    (hL : 0 < L) (hf : IsModel f b L) (Eig : E d → E d → ℝ × E d) (δ μ₁ μ₃ μ₄ : ℝ)
    (hδ : 0 < δ) (hμ₁ : 0 < μ₁) (hμ₃ : 0 < μ₃) (hμ₄ : 0 ≤ μ₄) (hEig : IsEigOracle f Eig μ₄)
    (ε σ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hσε : σ ≤ 1 / Real.sqrt (ε * d)) (xs ys : E d)
    (hhint : ∀ x : E d, Integrable
      (fun ζ : E d => hTrunc f L Eig δ μ₁ μ₃ ε xs (x + σ • ζ) ys) (stdGaussian (E d)))
    (hgint : ∀ x : E d, Integrable
      (fun ζ : E d => gTrunc f L ε xs (x + σ • ζ) ys) (stdGaussian (E d)))
    (h32 : ∀ x y : E d, hEps f L Eig δ μ₁ μ₃ ε x y ≤ greedyMax f L ε x y)
    (h33 : hEps f L Eig δ μ₁ μ₃ ε xs ys = greedyMax f L ε xs ys)
    (h34 : ∫ ζ, ‖stochGrad f L Eig δ μ₁ μ₃ ε σ xs xs ys ζ‖ ∂(stdGaussian (E d)) ≤
      (1 / 8000) * (σ ^ 14 * ε ^ (3 / 2 : ℝ) / b ^ 2))
    (h3536 : ∃ (H' : E d → (E d →L[ℝ] ℝ)) (H'' : E d →L[ℝ] E d →L[ℝ] ℝ),
      (∀ᶠ x in 𝓝 xs, HasFDerivAt (fun x' => hSmooth f L Eig δ μ₁ μ₃ ε σ xs x' ys) (H' x) x) ∧
      HasFDerivAt H' H'' xs ∧
      ‖H' xs‖ ≤ ε ^ 2 * σ ^ 7 / (8000 * b) ∧
      ∀ v : E d, -(Real.sqrt ε / 5) * ‖v‖ ^ 2 ≤ H'' v v) :
    IsApproxLocalMinDisc (fun x => greedyMax f L ε x ys) ε σ xs := by sorry

end GreedyAdvEq.Existence
