-- Prove2me | Theorems.Thm_HatAffineGeneral_q3F_affine
-- name    : HatAffineGeneral.q3F_affine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T09:13:45.90884+00:00
-- url     : https://prove2.me/theorems/8fce7dd7-e568-542f-a9eb-3f91ff80945e
-- title:
--   Hat Affine General: q3 F affine
-- statement:
--   The Hat Affine General construction uses the q3 F affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGeneral/Discovery.lean#L86-L89
-- source:
--   https://github.com/insammael/one-sided-affine-hat-guessing/blob/991721669233b41666e6f56b1471e58eb63d719e/HatAffineGeneral/Discovery.lean#L86-L89

import Mathlib
import Definitions.Def_HatAffineGeneral_Discovery
set_option autoImplicit true
open scoped BigOperators
open HatAffineGeneral
universe u v w
attribute [local instance] HatAffineGeneral.three_is_prime

theorem HatAffineGeneral.q3F_affine : AffineHalf q3F := by sorry
