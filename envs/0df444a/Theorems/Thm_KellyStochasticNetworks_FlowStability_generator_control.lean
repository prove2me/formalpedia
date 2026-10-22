-- Prove2me | Theorems.Thm_KellyStochasticNetworks_FlowStability_generator_control
-- name    : KellyStochasticNetworks.FlowStability.generator_control
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:50:14.269958+00:00
-- url     : https://prove2.me/theorems/6f24c2d7-9439-40a4-bee8-37793da9541e
-- title:
--   Exercise D.2 — true generator remainder and drift control
-- statement:
--   Let $X$ be a weighted $\alpha$-fair policy, let $Q$ be the flow-count generator, and let $L$ and $H$ be the Lyapunov function and first-order expression from (8.3). For every $\eta>0$ there exists $b\ge0$, independent of the count vector, such that
--   $$QL(n)\le H(n)+\eta\sum_r n_r^\alpha+b\qquad(n\in\mathbb N^R).$$
--   Under $A\rho<C$, there are $\epsilon>0$, a natural-number threshold $K$, and a real constant $b$ such that
--   $$QL(n)\le\begin{cases}b-\epsilon,&\sum_r n_r\le K,\\-\epsilon,&\sum_r n_r>K.\end{cases}$$
--   Thus the actual drift, including arrivals into empty coordinates, satisfies the finite-exception-set condition requested by the appendix. This is the continuous-time generator completion of the chapter's first-order calculation.
--
--   **Formalization Note** The open-ended exercise is instantiated as a uniform remainder estimate and its requested Foster drift consequence. Constants may depend on the fixed network and, for the first bound, on $\eta$, but never on $n$. The exception set uses total occupancy and is finite. No finite-time conditional increment is silently replaced by its infinitesimal derivative; no unspecified big-O bound is used.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 215 (PDF p. 223), Exercise D.2; printed pp. 190–191 (PDF pp. 198–199), proof of Theorem 8.2

import Mathlib
import Definitions.Def_KellyStochasticNetworks_FlowStability_Process

namespace KellyStochasticNetworks.FlowStability

/-- Exercise D.2: uniform generator remainder and the finite-exception-set drift
condition, for the exact Lyapunov function of the proof of Theorem 8.2. -/
theorem generator_control {J R : ℕ} (D : Network J R)
    (X : State R → Fin R → ℝ) (hX : IsAlphaFair D X) :
    (∀ eta : ℝ, 0 < eta → ∃ b : ℝ, 0 ≤ b ∧ ∀ n : State R,
      generator D X (lyapunov D) n ≤ firstOrderDrift D X n +
        eta * (∑ r, (n r : ℝ) ^ D.alpha) + b) ∧
    (Subcritical D → ∃ epsilon : ℝ, 0 < epsilon ∧ ∃ K : ℕ, ∃ b : ℝ,
      ∀ n : State R, generator D X (lyapunov D) n ≤
        if (∑ r, n r) ≤ K then b - epsilon else -epsilon) := by sorry

end KellyStochasticNetworks.FlowStability
