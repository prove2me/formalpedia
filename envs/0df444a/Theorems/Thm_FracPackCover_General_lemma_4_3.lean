-- Prove2me | Theorems.Thm_FracPackCover_General_lemma_4_3
-- name    : FracPackCover.General.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:20:20.443081+00:00
-- url     : https://prove2.me/theorems/7971535f-bee2-4dd7-8a68-5fec5c0fe458
-- title:
--   Lemma 4.3 — a step toward the oracle point lowers Φ by at least ασλΦ/30
-- statement:
--   Let $A, b, d > 0, P$ be as in the GENERAL problem with $P$ convex, and let $\rho > 0$ bound the width: $|a_i x - b_i| \le \rho d_i$ for all $x \in P$ and all $i$. Let $x \in P$, $\lambda = \lambda(x)$, $\varepsilon \in (0,1)$, $\alpha > 0$, let $y$ be the dual solution of $x$ and $\Phi = y^t d = \sum_i e^{\alpha(a_ix-b_i)/d_i}$. Let $\tilde x \in P$ attain $C_{\mathcal G}(y)$ and suppose $(x,\lambda)$ and $y$ do not satisfy $(\mathcal G2)$. If $0 \le \sigma \le \lambda/(24\alpha\rho^2)$, $\hat x = (1-\sigma)x + \sigma \tilde x$ and $\hat\Phi$ is the potential of $\hat x$ (same $\alpha$), then
--   $$\Phi - \hat\Phi \ \ge\ \frac{\alpha\sigma\lambda\,\Phi}{30}.$$
--
--   This is the progress lemma: each update of IMPROVE-GENERAL lowers the potential by a fixed fraction, which bounds the number of iterations.
--
--   **Formalization Note.** The paper writes $\Phi - \hat\Phi = \Omega(\alpha\sigma\lambda\Phi)$; its proof yields $\Phi - \hat\Phi > \alpha\sigma(\lambda/5 - 4\alpha\sigma\rho^2)\Phi \ge \alpha\sigma\lambda\Phi/30$, and the explicit constant $1/30$ is stated. The error parameter $\varepsilon$ appears in the printed statement but plays no role; it is kept as a hypothesis. The non-strict inequality covers $\sigma = 0$.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), pp. 26–27, Lemma 4.3 and its proof

import Mathlib
import Definitions.Def_FracPackCover_General_Basic

namespace FracPackCover.General

/-- Lemma 4.3 (pp. 26–27), with the explicit constant of its proof. Let `x ∈ P`, `λ = λ(x)`,
`α > 0`, `y` the dual solution of `x`, `Φ` its potential, and suppose `(x, λ)` and `y` violate (𝒢2)
where `x̃ ∈ P` attains `C_𝒢(y)`. If `0 ≤ σ ≤ λ/(24αρ²)` and `x̂ = (1 − σ)x + σx̃`, then
`Φ − Φ̂ ≥ ασλΦ/30` (the paper writes `Ω(ασλΦ)`). The error parameter `ε ∈ (0,1)` of the printed
statement is kept but unused. -/
theorem lemma_4_3 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (x : Fin n → ℝ) (hx : x ∈ P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (α : ℝ) (hα : 0 < α)
    (xt : Fin n → ℝ) (hxt : xt ∈ P)
    (hmin : ∀ x' ∈ P, lagr A b (dualVec A b d α x) xt ≤ lagr A b (dualVec A b d α x) x')
    (hnG2 : ¬ G2 A b d x (lam A b d x) (dualVec A b d α x)
      (lagr A b (dualVec A b d α x) xt))
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ ≤ lam A b d x / (24 * α * ρ ^ 2)) :
    α * σ * lam A b d x * potential A b d α x / 30 ≤
      potential A b d α x - potential A b d α ((1 - σ) • x + σ • xt) := by sorry

end FracPackCover.General
