-- Prove2me | Theorems.Thm_IsWeakN_isVeryWeakN
-- name    : IsWeakN.isVeryWeakN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T15:07:47.348726+00:00
-- url     : https://prove2.me/theorems/c5892999-6615-4c97-adb0-66a47430a66a
-- title:
--   Is Weak N: is Very Weak N
-- statement:
--   Every weak N is a very weak N
--
--   Source: https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L553-L554
-- source:
--   https://github.com/gjenca/n-free-posets-and-orthomodularity/blob/468773e0343d048a6c2028357694661b3374f51a/Basic.lean#L553-L554

import Mathlib
import Definitions.Def_Basic
set_option autoImplicit true
variable {O : Type*} [Orthoset O]
variable {P : Type*} [PartialOrder P]

theorem IsWeakN.isVeryWeakN {a b c d : P} (h : IsWeakN a b c d) : IsVeryWeakN a b c d := by sorry
