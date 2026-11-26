-- Prove2me | Theorems.Thm_O3_aboveGeometricSum_le
-- name    : O3.aboveGeometricSum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:24.599504+00:00
-- url     : https://prove2.me/theorems/64dd33b6-badc-5b99-918c-46057fbe9bb6
-- title:
--   O3: above Geometric Sum le
-- statement:
--   For ratio bigger than one, the geometric work is controlled by its end.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L264-L277
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L264-L277

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveGeometricSum_le {c ratio : ℝ}
    (hc : 0 ≤ c) (hratio : 1 < ratio) (S : ℕ) :
    ∑ s ∈ Finset.range S, c * ratio ^ s ≤
      c * ratio ^ S / (ratio - 1) := by sorry
