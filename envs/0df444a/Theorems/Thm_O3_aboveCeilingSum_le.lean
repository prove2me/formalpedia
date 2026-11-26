-- Prove2me | Theorems.Thm_O3_aboveCeilingSum_le
-- name    : O3.aboveCeilingSum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:48.961842+00:00
-- url     : https://prove2.me/theorems/d703e31d-6d4f-42a4-b00a-488efe145379
-- title:
--   O3: above Ceiling Sum le
-- statement:
--   The exact ceiling ledger: one ceiling at each of `S` levels contributes at
--   most `S` above the corresponding real-valued work.  This is the corrected
--   overhead in TeX lines 484--492.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L247-L255
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L247-L255

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveCeilingSum_le (S : ℕ) (work : Fin S → ℝ)
    (hwork : ∀ s, 0 ≤ work s) :
    ∑ s, (Nat.ceil (work s) : ℝ) ≤ (∑ s, work s) + S := by sorry
