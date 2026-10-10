-- Prove2me | Theorems.Thm_NAGFlow_Implicit_theorem_4_1
-- name    : NAGFlow.Implicit.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:31:57.23612+00:00
-- url     : https://prove2.me/theorems/bf3c6d25-c44d-4aa0-8a6b-8f1be313c09b
-- title:
--   Theorem 4.1, p. 17 — for f ∈ S¹_μ, μ ≥ 0, the implicit scheme (72)–(73) with α_k > 0 has ℒ_{k+1} ≤ ℒ_k/(1 + α_k)
-- statement:
--   Let $V$ be a real Hilbert space and $f\in\mathcal S^1_\mu$ with $\mu\ge0$: $f$ is continuously differentiable and
--   $$f(x)-f(y)-\langle\nabla f(y),x-y\rangle\ \ge\ \frac\mu2\|x-y\|^2\qquad\forall x,y\in V.$$
--   Let $x^*$ be a global minimiser of $f$. Consider sequences $(x_k),(v_k)$ in $V$ and real sequences $(\alpha_k),(\gamma_k)$ with $\gamma_0>0$ that satisfy, for every $k\in\mathbb N$, $\alpha_k>0$ and the implicit scheme
--   $$\frac{x_{k+1}-x_k}{\alpha_k}=v_{k+1}-x_{k+1},\qquad \frac{v_{k+1}-v_k}{\alpha_k}=\frac{\mu}{\gamma_k}(x_{k+1}-v_{k+1})-\frac1{\gamma_k}\nabla f(x_{k+1}),\qquad\frac{\gamma_{k+1}-\gamma_k}{\alpha_k}=\mu-\gamma_{k+1}.$$
--   With the Lyapunov function $\mathcal L_k=f(x_k)-f(x^*)+\frac{\gamma_k}2\|v_k-x^*\|^2$,
--
--   $$\mathcal L_{k+1}\ \le\ \frac{\mathcal L_k}{1+\alpha_k}\qquad\text{for all }k\in\mathbb N .$$
--
--   The fully implicit discretization of the NAG flow therefore contracts its Lyapunov function at every step, for any positive step sizes and for merely convex $f$ ($\mu=0$); with $\alpha_k\ge\alpha>0$ the rate is linear. This is the discrete counterpart of the exponential decay $\mathcal L(t)\le e^{-t}\mathcal L(0)$ of the flow, and the template the paper's semi-implicit and explicit schemes are measured against.
--
--   **Formalization Note.** The scheme's equations are hypotheses on the sequences: the theorem covers every run, and does not claim a run exists. No Lipschitz condition on $\nabla f$ and no relation between $\alpha_k$ and $\gamma_k$ is assumed. The parameter equation (73) and $\gamma_0>0$ are included because (72) uses $\gamma_k$, defined by (73) on p. 16. Inner product and duality pairing are both the real inner product (Riesz); the gradient is an explicit map with `HasGradientAt` at every point and continuous.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, Theorem 4.1, p. 17; (2) p. 2; (72), (73), (74) p. 16

import Mathlib
import Definitions.Def_NAGFlow_Implicit_Setting

namespace NAGFlow.Implicit

/-- Theorem 4.1, p. 17: let `f ∈ S¹_μ` with gradient map `gradf` and `μ ≥ 0`, and let `x*` be a
global minimiser of `f`. For every run of the implicit scheme (72) with the parameter equation
(73), `γ₀ > 0` and step sizes `α_k > 0`,
`ℒ_{k+1} ≤ ℒ_k / (1 + α_k)` for all `k ∈ ℕ`. -/
theorem theorem_4_1 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] (f : V → ℝ) (gradf : V → V) (μ : ℝ) (hf : NAGFlow.PredCorr.IsS1 f gradf μ)
    (xstar : V) (hxstar : ∀ y, f xstar ≤ f y)
    (α γ : ℕ → ℝ) (x v : ℕ → V) (hrun : IsImplicitRun gradf μ α γ x v) :
    ∀ k : ℕ, lyap f xstar x v γ (k + 1) ≤ lyap f xstar x v γ k / (1 + α k) := by sorry

end NAGFlow.Implicit
