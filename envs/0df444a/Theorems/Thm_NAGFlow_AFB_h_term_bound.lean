-- Prove2me | Theorems.Thm_NAGFlow_AFB_h_term_bound
-- name    : NAGFlow.AFB.h_term_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:43:16.006484+00:00
-- url     : https://prove2.me/theorems/33370e22-17f3-47f5-b048-ecf668ee4bfb
-- title:
--   Proof of Theorem 7.3, pp. 34–35 — x_{k+1} − y_k = (α_k/(1 + α_k))(v_{k+1} − v_k) and the h-terms of (123) are ≤ 0
-- statement:
--   Let $V$ be a real Hilbert space, let $(Q,h,g)$ be an instance of the composite problem (104) with constants $0\le\mu\le L$, and let $(x_k,y_k,w_k,v_k)$ with parameters $(\alpha_k,\gamma_k)$ be a run of Algorithm 4 (Semi-AFB), so that $L\alpha_k^2=\gamma_k(1+\alpha_k)$. Then for every $k$:
--
--   1. $$x_{k+1}-y_k=\frac{\alpha_k}{1+\alpha_k}(v_{k+1}-v_k);$$
--   2. $$(1+\alpha_k)\bigl(h(x_{k+1})-h(y_k)\bigr)-\alpha_k\langle\nabla h(y_k),v_{k+1}-v_k\rangle-\frac{\gamma_k}{2}\|v_{k+1}-v_k\|^2\ \le\ \frac{L\alpha_k^2}{2(1+\alpha_k)}\|v_{k+1}-v_k\|^2-\frac{\gamma_k}{2}\|v_{k+1}-v_k\|^2;$$
--   3. the right-hand side of 2 equals $0$.
--
--   Together these show that the $h$-terms of (123) are nonpositive; the step relation $L\alpha_k^2=\gamma_k(1+\alpha_k)$ is chosen exactly so that the bound in 2 vanishes.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 7.3, displays after (123), pp. 34–35

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace NAGFlow.AFB

/-- The bound on the `h`-terms of (123), pp. 34–35 (Luo & Chen, arXiv:1909.03145v4). For a run of
Algorithm 4 for (104) and every `k`:
1. `x_{k+1} − y_k = (α_k/(1 + α_k))(v_{k+1} − v_k)`;
2. `(1 + α_k)(h(x_{k+1}) − h(y_k)) − α_k⟪∇h(y_k), v_{k+1} − v_k⟫ − (γ_k/2)‖v_{k+1} − v_k‖²
   ≤ (Lα_k²/(2(1 + α_k)))‖v_{k+1} − v_k‖² − (γ_k/2)‖v_{k+1} − v_k‖²`;
3. the right-hand side of 2 equals `0` (as `Lα_k² = γ_k(1 + α_k)`). -/
theorem h_term_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v) :
    ∀ k : ℕ, x (k + 1) - y k = (α k / (1 + α k)) • (v (k + 1) - v k) ∧
      (1 + α k) * (h (x (k + 1)) - h (y k)) - α k * inner ℝ (gradh (y k)) (v (k + 1) - v k) -
          γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 ≤
        L * α k ^ 2 / (2 * (1 + α k)) * ‖v (k + 1) - v k‖ ^ 2 -
          γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 ∧
      L * α k ^ 2 / (2 * (1 + α k)) * ‖v (k + 1) - v k‖ ^ 2 -
          γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 = 0 := by sorry

end NAGFlow.AFB
