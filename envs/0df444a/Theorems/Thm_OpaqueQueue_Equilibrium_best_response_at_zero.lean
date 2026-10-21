-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_best_response_at_zero
-- name    : OpaqueQueue.Equilibrium.best_response_at_zero
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:57.850679+00:00
-- url     : https://prove2.me/theorems/a4f1274e-9f3d-4f9d-9ee0-165ae54c7b07
-- title:
--   Proof of Theorem 1, pp. 33–34 (PDF 34–35) — at q = 0 the law is g0(0) = 1, gn(0) = 0, and the best response is π̄(0) = 1
-- statement:
--   Under the standing assumptions, take $q=0$. Then $\pi_n(0)=0$ for all $n$, so the steady-state law (21) is the point mass at the empty system:
--   $$g_0(0)=1,\qquad g_n(0)=0\ \ (n\ge1),$$
--   and the customer's problem (9) under this prior has the unique solution $\bar\pi(0)=1$: a customer who is certain the system is empty joins with certainty.
--
--   This is the left endpoint of the fixed-point argument: the best response at $q=0$ lies strictly above $q$.
--
--   **Formalization Note** The page computes $\bar\pi(0)$ through the consistency map (22); the formalization states it for the maximizer of (9), which is the best response used in the rest of the proof. Uniqueness of the maximizer at $q = 0$ uses $v_0>0$, i.e. $R>p$.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), pp. 33–34 (PDF 34–35), proof of Theorem 1, Existence

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem best_response_at_zero (P : Params) (hS : P.Standing) : stat P 0 0 = 1 ∧ (∀ n : ℕ, 1 ≤ n → stat P 0 n = 0) ∧ ∀ x : ℝ, IsOptimal P (stat P 0) x ↔ x = 1 := by sorry
end OpaqueQueue.Equilibrium
