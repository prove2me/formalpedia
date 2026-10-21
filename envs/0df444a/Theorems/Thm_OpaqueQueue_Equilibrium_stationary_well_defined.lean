-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_stationary_well_defined
-- name    : OpaqueQueue.Equilibrium.stationary_well_defined
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:59.127897+00:00
-- url     : https://prove2.me/theorems/5036507d-0d05-4126-9562-164493041dff
-- title:
--   Proof of Theorem 1, p. 33 (PDF 34) — the steady-state law (21) is well-defined for every q < 1, and for q = 1 iff λ < µ
-- statement:
--   Consider the queue with rationally inattentive customers under the standing assumptions $\lambda,\mu,C,\theta>0$ and $R>p$. For an unconditional joining probability $q$, let $\pi_n(q)=q e^{v_n/\theta}/(1-q+qe^{v_n/\theta})$ be the conditional joining probabilities and
--   $$a_k(q) = \rho^k\,\pi_0(q)\pi_1(q)\cdots\pi_{k-1}(q) = \frac{\lambda_0\lambda_1\cdots\lambda_{k-1}}{\mu^k},\qquad \lambda_n=\lambda\pi_n(q),\ \rho=\lambda/\mu,$$
--   the unnormalized steady-state weights of the birth–death queue with arrival rates $\lambda_n$ and service rate $\mu$. Then:
--
--   1. for every $q\in[0,1)$ the series $\sum_{k} a_k(q)$ converges;
--   2. at $q=1$ the series converges if and only if $\lambda<\mu$.
--
--   So the steady-state law (21) exists for every unconditional joining probability below one, and for "everyone joins" exactly when the queue is stable in the classical sense. This determines the set of $q$ on which the equilibrium analysis takes place.
--
--   **Formalization Note** The paper's proof also mentions $\theta=0$ and $\theta=\infty$; only $\theta>0$ (the setting of Definition 1) is formalized. Part 2 renders the paper's remark that for $\lambda\ge\mu$ the equilibrium joining probability cannot be $1$.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 33 (PDF 34), proof of Theorem 1, first paragraph

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem stationary_well_defined (P : Params) (hS : P.Standing) : (∀ q ∈ Set.Ico (0 : ℝ) 1, Summable (weight P q)) ∧ (Summable (weight P 1) ↔ P.lam < P.mu) := by sorry
end OpaqueQueue.Equilibrium
