-- Prove2me | Theorems.Thm_NAGFlow_AFB_diff_identity
-- name    : NAGFlow.AFB.diff_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:44:21.957063+00:00
-- url     : https://prove2.me/theorems/8b312d50-9872-4489-8469-8b5a6978483a
-- title:
--   Proof of Theorem 7.3, p. 33 — ℒ_{k+1} − ℒ_k = f(x_{k+1}) − f(x_k) + (α_k/2)(μ − γ_{k+1})‖v_{k+1} − x*‖² + γ_k(v_{k+1} − v_k, v_{k+1} − x*) − (γ_k/2)‖v_{k+1} − v_k‖²
-- statement:
--   Let $V$ be a real Hilbert space, let $(Q,h,g)$ be an instance of the composite problem (104) with constants $0\le\mu\le L$, let $x^*$ minimise $f=h+g$ over $Q$, and let $(x_k,y_k,w_k,v_k)$ with parameters $(\alpha_k,\gamma_k)$ be a run of Algorithm 4 (Semi-AFB). With $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}{2}\|v_k-x^*\|^2$, for every $k$,
--   $$\mathcal L_{k+1}-\mathcal L_k=f(x_{k+1})-f(x_k)+\frac{\alpha_k}{2}(\mu-\gamma_{k+1})\|v_{k+1}-x^*\|^2+\gamma_k\langle v_{k+1}-v_k,v_{k+1}-x^*\rangle-\frac{\gamma_k}{2}\|v_{k+1}-v_k\|^2.$$
--
--   This identity opens the proof of Theorem 7.3: it isolates the cross term $\gamma_k\langle v_{k+1}-v_k,v_{k+1}-x^*\rangle$, which is then controlled by the optimality of the proximal step.
--
--   **Formalization Note.** The values of $f$ are real numbers, $f=h+g$ with $g$ encoded by its finite values (see the definition file).
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 7.3, first display, p. 33

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace NAGFlow.AFB

/-- The difference identity at the start of the proof of Theorem 7.3, p. 33 (Luo & Chen,
arXiv:1909.03145v4). For a run of Algorithm 4 for (104), a minimiser `x*` of `f = h + g` over `Q`, and
`ℒ_k = f(x_k) − f(x*) + (γ_k/2)‖v_k − x*‖²`, for every `k`,
`ℒ_{k+1} − ℒ_k = f(x_{k+1}) − f(x_k) + (α_k/2)(μ − γ_{k+1})‖v_{k+1} − x*‖²
  + γ_k⟪v_{k+1} − v_k, v_{k+1} − x*⟫ − (γ_k/2)‖v_{k+1} − v_k‖²`. -/
theorem diff_identity {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v)
    (xstar : V) (hxstar : IsMinimizer h g D Q xstar) :
    ∀ k : ℕ, lyap h g xstar x v γ (k + 1) - lyap h g xstar x v γ k =
      fObj h g (x (k + 1)) - fObj h g (x k) +
        α k / 2 * (μ - γ (k + 1)) * ‖v (k + 1) - xstar‖ ^ 2 +
        γ k * inner ℝ (v (k + 1) - v k) (v (k + 1) - xstar) -
        γ k / 2 * ‖v (k + 1) - v k‖ ^ 2 := by sorry

end NAGFlow.AFB
