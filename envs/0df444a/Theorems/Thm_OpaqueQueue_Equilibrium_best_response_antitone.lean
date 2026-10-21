-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_best_response_antitone
-- name    : OpaqueQueue.Equilibrium.best_response_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:16:18.089972+00:00
-- url     : https://prove2.me/theorems/984d9051-de5b-4e05-96fe-6798dc490622
-- title:
--   Proof of Theorem 1, p. 34 (PDF 35) — the maximizer π̄(q) of (23) is decreasing in q
-- statement:
--   Under the standing assumptions, let $q\le q'$ both be admissible, let $x$ solve the customer's problem (23) under the prior $g(q)$ and $x'$ solve it under $g(q')$. Then
--   $$x'\le x .$$
--   That is, the best response $\bar\pi(q)$ is a (weakly) decreasing function of the unconditional joining probability $q$ that the customer anticipates: the more others join, the less she does.
--
--   Combined with the existence of a fixed point, this gives uniqueness of the equilibrium: a decreasing function can cross the identity at most once.
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 34 (PDF 35), proof of Theorem 1, Uniqueness, last paragraph

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem best_response_antitone (P : Params) (hS : P.Standing) (q q' x x' : ℝ) (hq : Admissible P q) (hq' : Admissible P q') (hle : q ≤ q') (hx : IsOptimal P (stat P q) x) (hx' : IsOptimal P (stat P q') x') : x' ≤ x := by sorry
end OpaqueQueue.Equilibrium
