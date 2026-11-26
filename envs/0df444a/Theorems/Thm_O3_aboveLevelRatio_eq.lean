-- Prove2me | Theorems.Thm_O3_aboveLevelRatio_eq
-- name    : O3.aboveLevelRatio_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:47.323986+00:00
-- url     : https://prove2.me/theorems/c1bba382-67b7-4e25-b294-865d9196a087
-- title:
--   O3: above Level Ratio eq
-- statement:
--   The source identity `Delta_0/delta=8 kappa^2/vartheta_p^2`.  It is the exact
--   input to the logarithmic restart-count statement.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L286-L292
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L286-L292

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveLevelRatio_eq {M D eps theta : ℝ}
    (hM : M ≠ 0) (heps : eps ≠ 0) (htheta : theta ≠ 0) :
    aboveInitialLevel M D /
        aboveTerminalLevel (theta * eps) M =
      8 * (aboveKappa M D eps) ^ 2 / theta ^ 2 := by sorry
