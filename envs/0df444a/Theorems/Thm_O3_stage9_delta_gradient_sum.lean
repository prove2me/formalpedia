-- Prove2me | Theorems.Thm_O3_stage9_delta_gradient_sum
-- name    : O3.stage9_delta_gradient_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:12.9306+00:00
-- url     : https://prove2.me/theorems/f4582ec4-3743-49e8-bbb7-1a2c7e9b0825
-- title:
--   O3: stage9 delta gradient sum
-- statement:
--   The partial weighted gradient sum equals `kappa_k p_k` whenever the
--   two exact scalar coefficient recurrences hold.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L181-L198
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L181-L198

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.stage9_delta_gradient_sum {d : ℕ}
    (N : ℕ) (theta kappa delta : ℕ → ℝ) (g : ℕ → Vec d)
    (hθ : ∀ k, theta k ≠ 0)
    (hδ : ∀ k, k < N → delta k = kappa (k + 1) / theta k)
    (hκ : ∀ k, k < N →
      kappa k = kappa (k + 1) * (1 - 1 / theta k)) :
    ∀ k, k ≤ N → ∑ j ∈ Finset.range k, delta j • g j =
      kappa k • stage9P theta g k := by sorry
