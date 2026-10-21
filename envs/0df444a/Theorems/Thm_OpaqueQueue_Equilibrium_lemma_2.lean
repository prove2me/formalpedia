-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_lemma_2
-- name    : OpaqueQueue.Equilibrium.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:12.630912+00:00
-- url     : https://prove2.me/theorems/e55ed6cb-77eb-4fc5-853c-a52db247f89b
-- title:
--   Lemma 2, p. 35 (PDF 36) — for 0 ≤ q1 < q2 ≤ 1, gn(q2) − gn(q1) is first negative, then positive in n
-- statement:
--   Under the standing assumptions, let $0\le q_1<q_2\le1$ both be admissible, and let $g(q_1)$, $g(q_2)$ be the corresponding steady-state laws (21). Then the difference $d_n = g_n(q_2)-g_n(q_1)$ changes sign exactly once, from negative to positive: there is an index $n_0\ge1$ with
--   $$d_n<0\ \ (n<n_0),\qquad d_{n_0}\ge0,\qquad d_n>0\ \ (n>n_0).$$
--
--   In words, a larger unconditional joining probability shifts the steady-state queue-length distribution upward in the single-crossing sense, which implies first-order stochastic dominance. The paper combines this with the monotonicity of $\varphi_n$ in (25) to show that the best response is decreasing.
--
--   **Formalization Note** The switch index $n_0$ is the only place where $d_n$ may vanish; the paper treats all differences as strictly signed. Admissibility of $q_2$ is a real restriction only at $q_2=1$, where the law exists exactly when $\lambda<\mu$.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 35 (PDF 36), Lemma 2

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem lemma_2 (P : Params) (hS : P.Standing) (q₁ q₂ : ℝ) (h₁ : Admissible P q₁) (h₂ : Admissible P q₂) (h12 : q₁ < q₂) : ∃ n₀ : ℕ, 1 ≤ n₀ ∧ (∀ n : ℕ, n < n₀ → stat P q₂ n - stat P q₁ n < 0) ∧ (∀ n : ℕ, n₀ ≤ n → 0 ≤ stat P q₂ n - stat P q₁ n) ∧ (∀ n : ℕ, n₀ < n → 0 < stat P q₂ n - stat P q₁ n) := by sorry
end OpaqueQueue.Equilibrium
