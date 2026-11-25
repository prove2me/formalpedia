-- Prove2me | Theorems.Thm_HatAffineGeneral_q3F_first
-- name    : HatAffineGeneral.q3F_first
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:14:04.934741+00:00
-- url     : https://prove2.me/theorems/61cf758b-3330-4dca-8ffa-3c529f7eea35
-- title:
--   Hat Affine General: q3 F first
-- statement:
--   The Hat Affine General construction uses the q3 F first property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGeneral/Discovery.lean#L91-L93
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGeneral/Discovery.lean#L91-L93

import Mathlib
import Definitions.Def_HatAffineGeneral_Discovery
set_option autoImplicit true
open scoped BigOperators
open HatAffineGeneral
universe u v w
attribute [local instance] HatAffineGeneral.three_is_prime

theorem HatAffineGeneral.q3F_first (y : Fin 2 → F3) :
    q3F y 0 = y 0 - y 1 := by sorry
