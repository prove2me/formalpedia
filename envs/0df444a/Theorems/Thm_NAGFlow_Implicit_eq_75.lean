-- Prove2me | Theorems.Thm_NAGFlow_Implicit_eq_75
-- name    : NAGFlow.Implicit.eq_75
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:32:05.845768+00:00
-- url     : https://prove2.me/theorems/98693004-ef4b-42e1-af7a-d04e18a2556c
-- title:
--   (75), p. 17 — one step of the implicit scheme gives ℒ_{k+1} − ℒ_k ≤ −α_kℒ_{k+1}
-- statement:
--   Let $V$ be a real Hilbert space and $f\in\mathcal S^1_\mu$ with $\mu\ge0$, i.e. $f$ is continuously differentiable and $f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ge\frac\mu2\|x-y\|^2$ for all $x,y$. Let $x^*$ be a global minimiser of $f$, and let $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}2\|v_k-x^*\|^2$ be the Lyapunov function (74). Fix $k$, suppose $\gamma_k>0$, and suppose step $k$ of the implicit scheme holds: $\alpha_k>0$,
--   $$\frac{x_{k+1}-x_k}{\alpha_k}=v_{k+1}-x_{k+1},\quad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(x_{k+1}-v_{k+1})-\frac1{\gamma_k}\nabla f(x_{k+1}),\quad \frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_{k+1}.$$
--   Then
--
--   $$\mathcal L_{k+1}-\mathcal L_k\ \le\ -\alpha_k\,\mathcal L_{k+1}.$$
--
--   This one-step inequality is equivalent to the contraction $\mathcal L_{k+1}\le\mathcal L_k/(1+\alpha_k)$ of Theorem 4.1, which the page reduces to it ("It suffices to prove").
--
--   **Formalization Note.** The step is arbitrary: no relation between $\alpha_k$ and $\gamma_k$ is assumed, and the existence of $(x_{k+1},v_{k+1})$ is not claimed. The hypothesis $\gamma_k>0$ is the one-step form of the run's $\gamma_0>0$ (it propagates through (73) because $\mu\ge0$, $\alpha_k>0$; see Remark 4.1). Inner product and duality pairing are both the real inner product (Riesz); the gradient is an explicit map with `HasGradientAt` at every point.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, (75), proof of Theorem 4.1, p. 17; (2) p. 2; (72)–(74) p. 16

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace NAGFlow.Implicit

/-- (75), proof of Theorem 4.1, p. 17: let `f ∈ S¹_μ` with gradient map `gradf` and `μ ≥ 0`, and
let `x*` be a global minimiser of `f`. If `γ_k > 0` and step `k` of (72)–(73) holds with
`α_k > 0`, then `ℒ_{k+1} - ℒ_k ≤ -α_k ℒ_{k+1}`. -/
theorem eq_75 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (x v : ℕ → V) (k : ℕ) (hγ : 0 < γ k)
    (hstep : IsImplicitStep gradf μ α γ x v k) :
    lyap f xstar x v γ (k + 1) - lyap f xstar x v γ k ≤ -α k * lyap f xstar x v γ (k + 1) := by sorry

end NAGFlow.Implicit
