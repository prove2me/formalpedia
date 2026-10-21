-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_consistency_eq_8
-- name    : OpaqueQueue.Equilibrium.consistency_eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:56.526062+00:00
-- url     : https://prove2.me/theorems/3ecd01e3-13f2-4833-88f0-b80d5819c925
-- title:
--   Eq. (8), p. 12 (PDF 13) — at an optimum of (9), π̄ satisfies the consistency equation (5) with πn given by (8)
-- statement:
--   Under the standing assumptions, let $g$ be a prior on the number of customers in the system with $g_n\ge0$, $\sum_n g_n=1$ and $\sum_n n g_n<\infty$. If $\bar\pi$ solves the customer's problem (9) under $g$, then the conditional joining probabilities given by the GMNL formula (8),
--   $$\pi_n = \frac{\bar\pi e^{v_n/\theta}}{\bar\pi e^{v_n/\theta}+1-\bar\pi},$$
--   satisfy the consistency requirement (5):
--   $$\bar\pi = \sum_{n\ge0}\pi_n\,g_n .$$
--
--   This is the statement that the unconditional probability returned by (9) is indeed the unconditional probability of joining implied by the conditional ones; in the equilibrium of Definition 1 it makes the consistency equation (15) a consequence of optimality.
--
--   **Formalization Note** The finite-mean hypothesis on the prior is the one of Lemma 1, under which problem (9) is finite on all of $[0,1]$.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 12 (PDF 13), eq. (8) and the sentence following it; eq. (5), p. 11 (PDF 12)

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem consistency_eq_8 (P : Params) (hS : P.Standing) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hgs : Summable g) (hg1 : ∑' n, g n = 1) (hgm : Summable (fun n : ℕ => (n : ℝ) * g n)) (x : ℝ) (hx : IsOptimal P g x) : x = ∑' n, joinProb P x n * g n := by sorry
end OpaqueQueue.Equilibrium
