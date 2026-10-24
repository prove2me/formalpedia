-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_theorem_1
-- name    : OpaqueQueue.Equilibrium.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:28.540188+00:00
-- url     : https://prove2.me/theorems/03bae388-0a9f-4022-aeb8-151cc1105ee9
-- title:
--   Theorem 1, p. 15 (PDF 16) — for θ > 0 the queue with rationally inattentive customers has a unique equilibrium (Definition 1)
-- statement:
--   Consider an M/M/1 FCFS queue with arrival rate $\lambda>0$ and service rate $\mu>0$, whose customers receive the reward $R$, pay the price $p<R$, incur the delay cost $C>0$ per unit time, and cannot observe the queue length: before deciding to join or balk each customer acquires information about the number $n$ of customers in the system at cost $\theta>0$ per unit of mutual information. The payoff of joining in state $n$ is $v_n=R-p-(C/\mu)n$.
--
--   An **equilibrium** (Definition 1) is an unconditional joining probability $\tilde\pi\in[0,1]$ together with
--
--   1. the conditional joining probabilities $\tilde\pi_n=\tilde\pi e^{v_n/\theta}/(1-\tilde\pi+\tilde\pi e^{v_n/\theta})$ (14),
--   2. the steady-state law $\tilde g$ of the birth–death queue with arrival rates $\lambda_n=\lambda\tilde\pi_n$ and service rate $\mu$, which must exist,
--
--   such that $\tilde\pi=\sum_n\tilde\pi_n\tilde g(n)$ (15) and $\tilde\pi$ solves the customer's problem
--   $$\max_{x\in[0,1]}\ \theta\sum_{n\ge0}\tilde g(n)\log\big(x e^{v_n/\theta}+1-x\big)$$
--   under the equilibrium prior $\tilde g$.
--
--   **Theorem 1.** There exists exactly one such $\tilde\pi$. Since $\tilde\pi_n$ and $\tilde g$ are determined by $\tilde\pi$, the whole equilibrium is unique.
--
--   The theorem shows that a queue with rationally inattentive customers is well posed for every positive information cost: customers' beliefs about congestion and their joining behaviour are mutually consistent in exactly one way, regardless of whether $\lambda<\mu$. This is the basis for the paper's comparative statics, pricing analysis and limits $\theta\to0$ (visible queue) and $\theta\to\infty$ (invisible queue).
--
--   **Formalization Note** Definition 1 prints only (14), (15) and the product-form law; optimality in (9) under the equilibrium prior is included because (14)–(15) alone are satisfied by $\tilde\pi=0$ for all parameters (and by $\tilde\pi=1$ when $\lambda<\mu$), and because the paper's proof defines the best response as the maximizer (23) and calls its fixed point the equilibrium of Definition 1. The positivity of $\lambda,\mu,C$ is implicit in the model and is stated; no relation between $\lambda$ and $\mu$ is assumed.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 15 (PDF 16), Theorem 1; Definition 1, pp. 14–15 (PDF 15–16)

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem theorem_1 (P : Params) (hS : P.Standing) : ∃! q : ℝ, IsEquilibrium P q := by sorry
end OpaqueQueue.Equilibrium
