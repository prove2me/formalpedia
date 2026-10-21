-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_best_response_continuous
-- name    : OpaqueQueue.Equilibrium.best_response_continuous
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:03.589881+00:00
-- url     : https://prove2.me/theorems/e7cca088-6527-4241-9cb0-8b4a2a67f662
-- title:
--   Proof of Theorem 1, p. 34 (PDF 35) — the best response q ↦ π̄(q) is continuous on the admissible set
-- statement:
--   Under the standing assumptions, let $\beta$ be any function that assigns to every admissible $q$ (that is, $q\in[0,1]$ with a well-defined steady-state law $g(q)$) a solution $\beta(q)$ of the customer's problem (23) under the prior $g(q)$. Then $\beta$ is continuous on the admissible set
--   $$\mathcal A = \{q\in[0,1] : \textstyle\sum_k \rho^k\pi_0(q)\cdots\pi_{k-1}(q)<\infty\},$$
--   which is $[0,1]$ when $\lambda<\mu$ and $[0,1)$ when $\lambda\ge\mu$.
--
--   Continuity of $h(q)=\bar\pi(q)-q$ is what lets the paper apply the intermediate value theorem to obtain an equilibrium.
--
--   **Formalization Note** The maximizer is unique for admissible $q$ (milestone on (23)), so any selection $\beta$ is the best response; quantifying over all selections avoids a choice-function definition with junk values off $\mathcal A$.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 34 (PDF 35), proof of Theorem 1, Existence (continuity of h)

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem best_response_continuous (P : Params) (hS : P.Standing) (β : ℝ → ℝ) (hβ : ∀ q, Admissible P q → IsOptimal P (stat P q) (β q)) : ContinuousOn β {q : ℝ | Admissible P q} := by sorry
end OpaqueQueue.Equilibrium
