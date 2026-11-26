-- Prove2me | Theorems.Thm_O3_aboveGeometricSum_eq
-- name    : O3.aboveGeometricSum_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:03:13.120831+00:00
-- url     : https://prove2.me/theorems/04894d73-a112-4b4d-b29e-b7f052e9d843
-- title:
--   O3: above Geometric Sum eq
-- statement:
--   Exact finite geometric-sum identity used in the restart count.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L258-L261
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L258-L261

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveGeometricSum_eq {c ratio : ℝ} (hratio : ratio ≠ 1) (S : ℕ) :
    ∑ s ∈ Finset.range S, c * ratio ^ s =
      c * ((ratio ^ S - 1) / (ratio - 1)) := by sorry
