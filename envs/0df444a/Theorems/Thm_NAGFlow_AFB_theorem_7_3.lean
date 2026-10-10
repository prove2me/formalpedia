-- Prove2me | Theorems.Thm_NAGFlow_AFB_theorem_7_3
-- name    : NAGFlow.AFB.theorem_7_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:13.881792+00:00
-- url     : https://prove2.me/theorems/b2dd9c0d-3d5c-41bb-b15a-073ed45d756e
-- title:
--   Theorem 7.3, p. 33 — Semi-AFB (Algorithm 4) has ℒ_{k+1} ≤ ℒ_k/(1 + α_k), (87) and (88)
-- statement:
--   Let $V$ be a real Hilbert space. Let $Q\subseteq V$ be closed and convex, let $h\in\mathcal S^{1,1}_{\mu,L}(Q)$ with $0\le\mu\le L<\infty$, and let $g:V\to\mathbb R\cup\{+\infty\}$ be proper, closed and convex with $Q\cap\operatorname{dom}g\ne\emptyset$ (problem (104)). Let $x^*$ minimise $f=h+g$ over $Q$. Let $(x_k,y_k,w_k,v_k)$ with parameters $(\alpha_k,\gamma_k)$ be a run of Algorithm 4 (Semi-AFB) whose initial point $x_0$ lies in $\operatorname{dom}g$, and let
--   $$\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2.$$
--   Then
--
--   1. for every $k\in\mathbb N$,
--   $$\mathcal L_{k+1}\le\frac{\mathcal L_k}{1+\alpha_k};\qquad(121)$$
--   2. for every $k\ge0$,
--   $$\mathcal L_k\le\mathcal L_0\times\min\left\{\frac{4L}{(\sqrt{\gamma_0}\,k+2\sqrt L)^2},\ \left(1+\sqrt{\frac{\min\{\gamma_0,\mu\}}{L}}\right)^{-k}\right\};\qquad(87)$$
--   3. for every $k\ge1$,
--   $$\mathcal L_k\le C_{\gamma_0,L}\times\min\left\{\frac{4}{k^2},\ \left(1+\sqrt{\frac{\min\{\gamma_0,\mu\}}{L}}\right)^{1-k}\right\},\qquad(88)$$
--   where
--   $$C_{\gamma_0,L}=\frac{L}{\gamma_0}\bigl(f(x_0)-f(x^*)\bigr)+\frac{L}{2}\|v_0-x^*\|^2.\qquad(89)$$
--
--   Semi-AFB treats $h$ explicitly and $g$ implicitly, keeps all iterates in $Q$, and needs one proximal computation of $g$ over $Q$ per iteration. The theorem gives it the accelerated rate $O(L/k^2)$ for $\mu=0$ and the accelerated linear rate $(1+\sqrt{\min\{\gamma_0,\mu\}/L})^{-k}$ for $\mu>0$, in one statement, for constrained composite problems where $\nabla h$ need not exist outside $Q$.
--
--   **Formalization Note.** $V^*$ is identified with $V$ (Riesz). $g$ is encoded by its domain $D$ and its finite values on $D$ (see the definition file); step 5's argmin over $Q$ is a minimiser over $Q\cap D$. The hypothesis $x_0\in\operatorname{dom}g$ is added to the page's input $x_0,v_0\in Q$: without it $\mathcal L_0=C_{\gamma_0,L}=+\infty$. The positivity $\gamma_0>0$, $\alpha_k>0$ and $L>0$ are the inputs of Algorithm 4; $\alpha_k$ is any positive solution of $L\alpha_k^2=\gamma_k(1+\alpha_k)$. No subgradient or variational-inequality hypothesis is made. When $\mu=0$ the second entry of each minimum equals $1$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Theorem 7.3 and (121), p. 33; (87)–(89), p. 21

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace NAGFlow.AFB

/-- Theorem 7.3 (Luo & Chen, arXiv:1909.03145v4, p. 33), with (87)–(89) of p. 21. Let `Q` be closed
and convex, `h ∈ S^{1,1}_{μ,L}(Q)` with `0 ≤ μ ≤ L < ∞`, `g` proper, closed and convex with domain `D`,
`Q ∩ D ≠ ∅` (problem (104)), and let `x*` minimise `f = h + g` over `Q`. For every run of Algorithm 4
whose initial point `x₀` lies in `dom g`, with `ℒ_k = f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`:
(121) `ℒ_{k+1} ≤ ℒ_k/(1 + α_k)` for every `k ∈ ℕ`;
(87) `ℒ_k ≤ ℒ₀ · min{4L/(√γ₀ k + 2√L)², (1 + √(min{γ₀, μ}/L))^{−k}}` for every `k ≥ 0`;
(88) `ℒ_k ≤ C_{γ₀,L} · min{4/k², (1 + √(min{γ₀, μ}/L))^{1−k}}` for every `k ≥ 1`, where
(89) `C_{γ₀,L} = (L/γ₀)(f(x₀) − f(x*)) + (L/2)‖v₀ − x*‖²`. -/
theorem theorem_7_3 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v)
    (xstar : V) (hxstar : IsMinimizer h g D Q xstar) (hx0D : x 0 ∈ D) :
    (∀ k : ℕ, lyap h g xstar x v γ (k + 1) ≤ lyap h g xstar x v γ k / (1 + α k)) ∧
      (∀ k : ℕ, lyap h g xstar x v γ k ≤
        lyap h g xstar x v γ 0 *
          min (4 * L / (Real.sqrt (γ 0) * k + 2 * Real.sqrt L) ^ 2)
            ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (-(k : ℤ)))) ∧
      (∀ k : ℕ, 1 ≤ k → lyap h g xstar x v γ k ≤
        (L / γ 0 * (fObj h g (x 0) - fObj h g xstar) + L / 2 * ‖v 0 - xstar‖ ^ 2) *
          min (4 / (k : ℝ) ^ 2) ((1 + Real.sqrt (min (γ 0) μ / L)) ^ (1 - (k : ℤ)))) := by sorry

end NAGFlow.AFB
