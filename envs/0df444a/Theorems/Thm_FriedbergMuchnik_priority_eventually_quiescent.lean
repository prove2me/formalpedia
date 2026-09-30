-- Prove2me | Theorems.Thm_FriedbergMuchnik_priority_eventually_quiescent
-- name    : FriedbergMuchnik.priority_eventually_quiescent
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-09T21:55:17.849714+00:00
-- url     : https://prove2.me/theorems/8386e140-4bd1-4bc1-b4ac-55bdfec5d56a
-- title:
--   Finite injury: eventual stabilization and absence of attention
-- statement:
--   For the fixed priority construction, let $E_s(q)$ be the follower and acted flag stored for requirement $q$ at stage $s$. Let $W_s(p)$ be the Boolean test that requirement $p$ requests attention at that stage. For every priority index $q\in\mathbb N$, there is a stage after activation such that
--
--   $$
--   \exists a>q\;\forall s\ge a,\qquad
--   E_s(q)=E_a(q)\quad\land\quad
--   \forall p\le q,\ W_s(p)=\mathrm{false}.
--   $$
--
--   Thus both the follower and its acted flag stabilize, and every requirement of higher or equal priority eventually stops requesting attention. The statement concerns the explicit scheduler and makes no assumption about correctness of its oracle simulations. It supplies the finite injury part of the verification independently of diagonalization.
-- source:
--   Arnold W. Miller, Lecture notes in Recursion Theory, December 3, 2008, Section 26, Theorem 26.2, pp. 51–54, https://people.math.wisc.edu/~awmille1/old/m773-07/recthy.pdf. The verification on pp. 53–54, Claim (1) and (3), and the induction on priority. This interface states stabilization of the complete entry and eventual absence of attention, as obtained from the least-attention scheduler and acted flags in the existing priorityStage implementation. An accompanying direct Lean proof checks this strengthening from the update rule.

import Definitions.Def_FriedbergMuchnik_Priority

namespace FriedbergMuchnik

theorem priority_eventually_quiescent (q : ℕ) :
    ∃ a : ℕ, q < a ∧ ∀ s : ℕ, a ≤ s →
      (priorityStage s).2[q]?.getD (0, false) =
        (priorityStage a).2[q]?.getD (0, false) ∧
      ∀ p : ℕ, p ≤ q → wantsAttention s (priorityStage s) p = false := by sorry

end FriedbergMuchnik
