-- Prove2me | Theorems.Thm_NAGFlow_AFB_eq_120
-- name    : NAGFlow.AFB.eq_120
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:49.654414+00:00
-- url     : https://prove2.me/theorems/2ed4b102-ebdb-459b-a04e-7150aa74eebc
-- title:
--   (120), p. 33 — under the optimality variational inequality for v_{k+1}, γ_k(v_{k+1} − v_k, v_{k+1} − x) ≤ μα_k(y_k − v_{k+1}, v_{k+1} − x) − α_k⟨∇h(y_k) + p_{k+1}, v_{k+1} − x⟩
-- statement:
--   Let $V$ be a real Hilbert space, let $(Q,h,g)$ be an instance of the composite problem (104) with constants $0\le\mu\le L$, and let $(x_k,y_k,w_k,v_k)$ with parameters $(\alpha_k,\gamma_k)$ be a run of Algorithm 4 (Semi-AFB). Fix $k$ and let $p_{k+1}\in\partial g(v_{k+1})$ be such that the first-order optimality condition for $v_{k+1}$ holds in the form of the variational inequality
--   $$\left\langle\nabla h(y_k)+\frac{\gamma_k+\mu\alpha_k}{\alpha_k}(v_{k+1}-w_k)+p_{k+1},\ x-v_{k+1}\right\rangle\ \ge\ 0\qquad\forall\,x\in Q.$$
--   Then for every $x\in Q$,
--   $$\gamma_k\langle v_{k+1}-v_k,v_{k+1}-x\rangle\ \le\ \mu\alpha_k\langle y_k-v_{k+1},v_{k+1}-x\rangle-\alpha_k\langle\nabla h(y_k)+p_{k+1},v_{k+1}-x\rangle.\qquad(120)$$
--
--   This is the variational inequality of step 5 rewritten in terms of the momentum variable $v_k$, after expanding $w_k$. It is the form in which the paper feeds the proximal step into the Lyapunov analysis of Theorem 7.3.
--
--   **Formalization Note.** The existence of a subgradient $p_{k+1}$ satisfying the variational inequality is a hypothesis of this statement, not a conclusion: the paper cites it as well known, but in general it requires a constraint qualification for the sum rule $\partial(g+i_Q)=\partial g+N_Q$, which (104) does not assume. $V^*$ is identified with $V$.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, §7.3, variational inequality before (120) and (120), p. 33

import Mathlib
import Definitions.Def_NAGFlow_AFB_Setting

namespace NAGFlow.AFB

/-- (120), p. 33 (Luo & Chen, arXiv:1909.03145v4), posed with its premise. For a run of Algorithm 4
for (104) and an index `k`, let `p_{k+1} ∈ ∂g(v_{k+1})` satisfy the variational inequality
`⟪∇h(y_k) + ((γ_k + μα_k)/α_k)(v_{k+1} − w_k) + p_{k+1}, x − v_{k+1}⟫ ≥ 0` for all `x ∈ Q`. Then for
every `x ∈ Q`,
`γ_k⟪v_{k+1} − v_k, v_{k+1} − x⟫ ≤ μα_k⟪y_k − v_{k+1}, v_{k+1} − x⟫ − α_k⟪∇h(y_k) + p_{k+1}, v_{k+1} − x⟫`.
The existence of such a `p_{k+1}` is not asserted. -/
theorem eq_120 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (h : V → ℝ) (gradh : V → V) (g : V → ℝ) (D Q : Set V) (μ L : ℝ)
    (hprob : IsAFBProblem h gradh g D Q μ L)
    (α γ : ℕ → ℝ) (x y w v : ℕ → V) (hrun : IsAFBRun gradh g D Q μ L α γ x y w v)
    (k : ℕ) (p : V) (hp : IsSubgrad g D (v (k + 1)) p)
    (hVI : ∀ z ∈ Q, 0 ≤ inner ℝ (gradh (y k) + ((γ k + μ * α k) / α k) • (v (k + 1) - w k) + p)
      (z - v (k + 1))) :
    ∀ z ∈ Q, γ k * inner ℝ (v (k + 1) - v k) (v (k + 1) - z) ≤
      μ * α k * inner ℝ (y k - v (k + 1)) (v (k + 1) - z) -
        α k * inner ℝ (gradh (y k) + p) (v (k + 1) - z) := by sorry

end NAGFlow.AFB
