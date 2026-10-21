-- Prove2me | Theorems.Thm_OpaqueQueue_Equilibrium_unique_maximizer
-- name    : OpaqueQueue.Equilibrium.unique_maximizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:15:57.352976+00:00
-- url     : https://prove2.me/theorems/6f614719-709c-46de-83a9-e4af67fea9e1
-- title:
--   Proof of Theorem 1, p. 34 (PDF 35) — for admissible q, f(·; q) of (24) is concave and (23) has exactly one solution
-- statement:
--   Under the standing assumptions, let $q$ be admissible: $q\in[0,1]$ and the steady-state law $g(q)$ of (21) exists. Then the objective
--   $$f(x;q) = \theta\sum_{n\ge0} g_n(q)\log\big(x e^{v_n/\theta}+1-x\big)\tag{24}$$
--   is concave in $x$ on $[0,1]$, and the problem
--   $$\bar\pi(q) := \arg\max_{x\in[0,1]} f(x;q)\tag{23}$$
--   has exactly one solution.
--
--   This makes the best response $\bar\pi(q)$ of a customer who believes the queue is in steady state under $q$ a well-defined function of $q$; Theorem 1 is the statement that this function has exactly one fixed point.
--
--   **Formalization Note** Uniqueness of the maximizer is part of the conclusion, as on the page ("the solution is unique").
-- source:
--   Canyakmaz & Boyacı, Opaque Queues: Service Systems with Rationally Inattentive Customers, ESMT Working Paper 18-04 (September 24, 2018), p. 34 (PDF 35), proof of Theorem 1, eqs. (23)–(24) and the sentence following them

import Mathlib
import Definitions.Def_OpaqueQueue_Equilibrium_Model

namespace OpaqueQueue.Equilibrium
theorem unique_maximizer (P : Params) (hS : P.Standing) (q : ℝ) (hq : Admissible P q) : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (obj P (stat P q)) ∧ ∃! x : ℝ, IsOptimal P (stat P q) x := by sorry
end OpaqueQueue.Equilibrium
