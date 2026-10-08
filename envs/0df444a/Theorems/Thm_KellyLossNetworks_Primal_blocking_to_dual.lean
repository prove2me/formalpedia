-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_blocking_to_dual
-- name    : KellyLossNetworks.Primal.blocking_to_dual
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:07:27.431582+00:00
-- url     : https://prove2.me/theorems/80a53e26-3311-4c2b-bcd0-8a8a12789cde
-- title:
--   Conditions on B imply a dual optimum
-- statement:
--   Let $\nu_r>0$, and suppose $B$ satisfies conditions (2.7), including $0\le B_j<1$. Then the multipliers
--
--   $$y_j=-\log(1-B_j)$$
--
--   minimize the dual objective $D(y)$ over $y\ge0$. This is the converse direction of the correspondence between dual optima and solutions of the blocking conditions.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 328, §2.1, one-to-one correspondence after (2.7)

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, p. 328, the converse direction of the
one-to-one correspondence after (2.7). -/
theorem blocking_to_dual {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (B : Fin J → ℝ) (hB : ConditionsOnB A ν C B) :
    IsDualOpt A ν C (dualFromBlocking B) := by sorry

end KellyLossNetworks.Primal
