-- Prove2me | Theorems.Thm_MohP3_FormalLocal_radical_Qk_le_ker
-- name    : MohP3.FormalLocal.radical_Qk_le_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:53:55.127268+00:00
-- url     : https://prove2.me/theorems/1187abd0-9f90-518a-b270-d6ff92ae34a0
-- title:
--   Formal Local: radical Qk le ker
-- statement:
--   One half of the formal-local statement, unconditionally.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L157-L160
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L157-L160

module
public import Definitions.Def_MohP3_Generic
public import Definitions.Def_MohP3_FormalLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.FormalLocal.radical_Qk_le_ker : (Qk k).radical ≤ RingHom.ker (psi k) := by sorry
