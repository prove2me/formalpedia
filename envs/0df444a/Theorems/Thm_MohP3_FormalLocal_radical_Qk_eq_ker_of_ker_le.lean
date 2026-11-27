-- Prove2me | Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_ker_of_ker_le
-- name    : MohP3.FormalLocal.radical_Qk_eq_ker_of_ker_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:19:40.875528+00:00
-- url     : https://prove2.me/theorems/86534411-ce5c-504b-af57-50a7195ec512
-- title:
--   Formal Local: radical Qk eq ker of ker le
-- statement:
--   The same corollary, phrased with the kernel identification as hypothesis.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L347-L352
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L347-L352

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

theorem MohP3.FormalLocal.radical_Qk_eq_ker_of_ker_le (hker : RingHom.ker (psi k) ≤ Pk k) :
    (Qk k).radical = RingHom.ker (psi k) := by sorry
