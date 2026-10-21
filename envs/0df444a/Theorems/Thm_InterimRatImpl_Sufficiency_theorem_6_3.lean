-- Prove2me | Theorems.Thm_InterimRatImpl_Sufficiency_theorem_6_3
-- name    : InterimRatImpl.Sufficiency.theorem_6_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:09:34.929845+00:00
-- url     : https://prove2.me/theorems/6d5a21e3-1a8c-4ca3-9d5d-46472246da21
-- title:
--   Theorem 6.3 — weak IRM and weak NWR suffice for implementation
-- statement:
--   Let $f:T\to\Delta(A)$ be a social choice function on a finite interim type space. Suppose another social choice function $\hat f$ agrees with $f$ on every state in the designer's target set $T^*$, and $\hat f$ satisfies weak interim rationalizable monotonicity and weak no-worst-rule. Then there is a mechanism with nonempty countable message spaces that implements $f$ in interim rationalizable strategies:
--
--   $$
--   \hat f\approx f,\quad \operatorname{WeakIRM}(\hat f),\quad
--   \operatorname{WeakNWR}(\hat f)
--   \quad\Longrightarrow\quad
--   \operatorname{Implementable}(f).
--   $$
--
--   Implementation means that every type has a rationalizable message and that every rationalizable message profile at every state yields the same social choice function equivalent to $f$ on $T^*$.
--
--   **Formalization Note** Each type set is nonempty, as implied by the paper's probability beliefs. The target set contains every state to which at least one agent assigns positive interim probability. No two-agent condition or canonical-mechanism parameter is imposed on the goal.
-- source:
--   Kunimoto, Saran & Serrano, Interim Rationalizable Implementation of Functions, Bravo Working Paper # 2020-023 (Brown University, version of October 2020), p. 19 (PDF 20), Theorem 6.3

import Definitions.Def_InterimRatImpl_Sufficiency_Model

namespace InterimRatImpl.Sufficiency

universe u v w
variable {I : Type u} [Fintype I] [DecidableEq I]
  {T : I → Type v} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
  [∀ i, Nonempty (T i)] {A : Type w} [Fintype A] [DecidableEq A]

/-- Theorem 6.3, p. 19: weak IRM and weak NWR suffice for interim
rationalizable implementation. -/
theorem theorem_6_3 (E : Env I T A) (Tstar : Set (Profile T))
    (hTstar : Support E ⊆ Tstar) (f fhat : SCF T A)
    (heq : Equiv Tstar fhat f) (hIRM : WeakIRM E fhat)
    (hNWR : WeakNWR E fhat) :
    Implementable E Tstar f := by sorry

end InterimRatImpl.Sufficiency
