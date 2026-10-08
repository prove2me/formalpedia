-- Prove2me | Theorems.Thm_KellyLossNetworks_Primal_change_of_variables
-- name    : KellyLossNetworks.Primal.change_of_variables
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:21.572991+00:00
-- url     : https://prove2.me/theorems/463fd37c-8e69-4bd1-99fe-c70eaf9626d8
-- title:
--   Equation (2.6): complementary conditions become conditions on B
-- statement:
--   For a multiplier vector $y$ and positive offered traffic, set $B_j=1-e^{-y_j}$. The primal and dual feasibility plus complementary slackness conditions (2.4)–(2.5) hold exactly when $B$ satisfies conditions (2.7): $0\le B_j<1$ and the route flow through each link equals $C_j$ if $B_j>0$, or is at most $C_j$ if $B_j=0$.
--
--   The equality uses $\prod_i(1-B_i)^{A_{ir}}=e^{-\sum_i y_iA_{ir}}$. It connects the multiplier and blocking descriptions without choosing a particular optimum.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 328, §2.1, (2.6)–(2.7)

import Mathlib
import Definitions.Def_KellyLossNetworks_Primal_Problem

namespace KellyLossNetworks.Primal

/-- Kelly, *Loss networks* (1991), §2.1, p. 328, (2.6)–(2.7).
The nonnegative multiplier condition is part of `complementary`. -/
theorem change_of_variables {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r)
    (y : Fin J → ℝ) :
    complementary A ν C y ↔ ConditionsOnB A ν C (blockingFromDual y) := by sorry

end KellyLossNetworks.Primal
