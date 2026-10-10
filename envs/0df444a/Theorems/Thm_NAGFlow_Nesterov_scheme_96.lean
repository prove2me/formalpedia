-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_scheme_96
-- name    : NAGFlow.Nesterov.scheme_96
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:19.70799+00:00
-- url     : https://prove2.me/theorems/bd0c4b13-6018-435a-bb0d-3823d079f7f6
-- title:
--   §6.2, p. 24 — Algorithm 1 is equivalent to the scheme (96) with (97) and Lα_k² = γ_{k+1}
-- statement:
--   Let $V$ be a real Hilbert space, $f:V\to\mathbb R$ with gradient map $\nabla f$, and $0\le\mu\le L$, $0<L$. Sequences $(\alpha_k,\gamma_k,x_k,y_k,v_k)_{k\ge0}$ form a run of Algorithm 1 (Nesterov's accelerated gradient method) if and only if $\gamma_0>0$ and, for every $k$, $\alpha_k>0$, $L\alpha_k^2=\gamma_{k+1}$,
--   $$\frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_k,\qquad \frac{y_k-x_k}{\alpha_k}=\frac{\gamma_k}{\gamma_{k+1}}(v_k-y_k),\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_{k+1}}(y_k-v_k)-\frac{1}{\gamma_{k+1}}\nabla f(y_k),\qquad(96)$$
--   and
--   $$f(x_{k+1})\le f(y_k)-\frac{1}{2L}\|\nabla f(y_k)\|^2.\qquad(97)$$
--
--   This is the observation that turns Nesterov's method into a discretization of the NAG flow: the $(y,v)$ updates are a semi-implicit scheme for the flow, the $\gamma$ update is an explicit scheme for its parameter equation, and (97) is a correction step.
--
--   **Formalization Note.** The paper says "after simple calculations, we can rewrite Algorithm 1 as an equivalent form"; the statement records both directions at the level of whole runs. The step rule $L\alpha_k^2=\gamma_{k+1}$ is the hypothesis of Theorem 6.1, which in Algorithm 1 is step 2 rewritten through step 3. $\|\cdot\|_*$ is the norm of $V$ (Riesz).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §6.2, (96)–(97), p. 24

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace NAGFlow.Nesterov

/-- §6.2, p. 24 (Luo & Chen, arXiv:1909.03145v4): Algorithm 1 is equivalent to the scheme (96)
together with (97) and the step rule `Lα_k² = γ_{k+1}`. For `0 ≤ μ ≤ L`, `0 < L`, sequences
`(α, γ, x, y, v)` form a run of Algorithm 1 if and only if `γ₀ > 0` and, for every `k`, `α_k > 0`,
`Lα_k² = γ_{k+1}`, the three lines of (96) hold, and
(97) `f(x_{k+1}) ≤ f(y_k) − (1/(2L))‖∇f(y_k)‖²`. -/
theorem scheme_96 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hμ : 0 ≤ μ) (hμL : μ ≤ L) (hL : 0 < L)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) :
    IsNAGRun f gradf μ L α γ x y v ↔
      (0 < γ 0 ∧ (∀ k, 0 < α k) ∧ (∀ k, L * α k ^ 2 = γ (k + 1)) ∧
        (∀ k, IsScheme96Step gradf μ (α k) (γ k) (γ (k + 1)) (x k) (y k) (v k) (v (k + 1))) ∧
        (∀ k, f (x (k + 1)) ≤ f (y k) - 1 / (2 * L) * ‖gradf (y k)‖ ^ 2)) := by sorry

end NAGFlow.Nesterov
