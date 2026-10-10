-- Prove2me | Theorems.Thm_NAGFlow_Nesterov_theorem_6_1
-- name    : NAGFlow.Nesterov.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:29.466794+00:00
-- url     : https://prove2.me/theorems/d2c1b328-7c73-4518-b539-e55237a05bcf
-- title:
--   Theorem 6.1, p. 24 — Nesterov's method (Algorithm 1) has 0 < α_k ≤ 1, ℒ_{k+1} ≤ (1 − α_k)ℒ_k, (99) and (100)
-- statement:
--   Let $V$ be a real Hilbert space and $f\in\mathcal S^{1,1}_{\mu,L}$ with $0\le\mu\le L<\infty$, that is, $f$ is continuously differentiable, $\mu$-convex, and has $L$-Lipschitz gradient. Let $x^*$ be a global minimiser of $f$. Let $(\alpha_k,\gamma_k,x_k,y_k,v_k)$ be a run of Nesterov's accelerated gradient method (Algorithm 1): $\gamma_0>0$, and for every $k$, $\alpha_k>0$ solves $L\alpha_k^2=(1-\alpha_k)\gamma_k+\mu\alpha_k$, $\gamma_{k+1}=(1-\alpha_k)\gamma_k+\mu\alpha_k$ (so $L\alpha_k^2=\gamma_{k+1}$), $y_k=(\alpha_k\gamma_kv_k+\gamma_{k+1}x_k)/(\gamma_k+\mu\alpha_k)$, $f(x_{k+1})\le f(y_k)-\frac1{2L}\|\nabla f(y_k)\|^2$, and $v_{k+1}=\frac1{\gamma_{k+1}}[(1-\alpha_k)\gamma_kv_k+\alpha_k(\mu y_k-\nabla f(y_k))]$. Let
--   $$\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2\qquad(74)$$
--   and $C_{\gamma_0,L}=\frac{L}{\gamma_0}\big(f(x_0)-f(x^*)\big)+\frac L2\|v_0-x^*\|^2$ (89). Then $0<\alpha_k\le1$ for every $k$,
--   $$\mathcal L_{k+1}\le(1-\alpha_k)\mathcal L_k,\qquad k\in\mathbb N,\qquad(98)$$
--   for all $k\ge0$
--   $$\mathcal L_k\le\mathcal L_0\times\min\left\{\frac{4L}{(\sqrt{\gamma_0}\,k+2\sqrt L)^2},\ \Big(1-\sqrt{\frac{\min\{\gamma_1,\mu\}}{L}}\Big)^{k}\right\},\qquad(99)$$
--   and for all $k\ge1$
--   $$\mathcal L_k\le C_{\gamma_0,L}\times\min\left\{\frac{4}{k^2},\ \Big(1-\sqrt{\frac{\min\{\gamma_1,\mu\}}{L}}\Big)^{k-1}\right\}.\qquad(100)$$
--
--   The theorem gives a Lyapunov-function proof of the optimal accelerated rates of Nesterov's method, simultaneously for the convex case ($\mu=0$, rate $O(1/k^2)$) and the strongly convex case ($\mu>0$, linear rate $1-\sqrt{\mu/L}$ once $\gamma_1\ge\mu$), interpreting the method as a corrected semi-implicit discretization of the NAG flow.
--
--   **Formalization Note.** $\langle\cdot,\cdot\rangle$ and $\|\cdot\|_*$ are the inner product and norm of $V$ (Riesz); $\nabla f$ is an explicit gradient map. Algorithm 1 writes $\alpha_k\in(0,1)$; the run records only $\alpha_k>0$ (the positive root of step 2), and $\alpha_k\le1$ is concluded. Step 5 is an inequality, so the theorem covers every sufficient-decrease choice of $x_{k+1}$. The theorem's hypothesis "$L\alpha_k^2=\gamma_{k+1}$" follows from steps 2–3 and is not restated. $\gamma_1$ is the value produced by the run. $C_{\gamma_0,L}$ is written out inline.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Theorem 6.1 and Eqs. (98)–(100), p. 24; (89), p. 21; (74), p. 16

import Mathlib
import Definitions.Def_NAGFlow_Nesterov_Setting

namespace NAGFlow.Nesterov

/-- Theorem 6.1 (Luo & Chen, arXiv:1909.03145v4, p. 24). Let `f ∈ S^{1,1}_{μ,L}` with
`0 ≤ μ ≤ L < ∞`, let `x*` be a global minimiser of `f`, and let `(α, γ, x, y, v)` be a run of
Algorithm 1 (equivalently, of (96)–(97) with `Lα_k² = γ_{k+1}`). Then, with `ℒ_k` the Lyapunov
function (74):
* `0 < α_k ≤ 1` for every `k`;
* (98) `ℒ_{k+1} ≤ (1 − α_k)ℒ_k` for every `k ∈ ℕ`;
* (99) `ℒ_k ≤ ℒ₀ · min{4L/(√γ₀ k + 2√L)², (1 − √(min{γ₁, μ}/L))^k}` for every `k ≥ 0`;
* (100) `ℒ_k ≤ C_{γ₀,L} · min{4/k², (1 − √(min{γ₁, μ}/L))^{k−1}}` for every `k ≥ 1`, where
  (89) `C_{γ₀,L} = (L/γ₀)(f(x₀) − f(x*)) + (L/2)‖v₀ − x*‖²`. -/
theorem theorem_6_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ L : ℝ) (hf : NAGFlow.PredCorr.IsS11 f gradf μ L)
    (xstar : V) (hxstar : ∀ z, f xstar ≤ f z)
    (α γ : ℕ → ℝ) (x y v : ℕ → V) (hrun : IsNAGRun f gradf μ L α γ x y v) :
    (∀ k : ℕ, 0 < α k ∧ α k ≤ 1) ∧
      (∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ (1 - α k) * lyap f xstar x v γ k) ∧
      (∀ k : ℕ, lyap f xstar x v γ k ≤
        lyap f xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 - Real.sqrt (min (γ 1) μ / L)) ^ k)) ∧
      (∀ k : ℕ, 1 ≤ k → lyap f xstar x v γ k ≤
        (L / γ 0 * (f (x 0) - f xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 - Real.sqrt (min (γ 1) μ / L)) ^ (k - 1))) := by sorry

end NAGFlow.Nesterov
