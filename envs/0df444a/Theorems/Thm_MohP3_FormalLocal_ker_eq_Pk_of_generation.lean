-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ker_eq_Pk_of_generation
-- name    : MohP3.FormalLocal.ker_eq_Pk_of_generation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:04.619602+00:00
-- url     : https://prove2.me/theorems/00e842a4-cafb-5d9e-a4ed-cf6754ae43f9
-- title:
--   Formal Local: ker eq Pk of generation
-- statement:
--   Granting the completed generation statement, `ker psi = Pk`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L333-L334
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L333-L334

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

theorem MohP3.FormalLocal.ker_eq_Pk_of_generation (hgen : Generation k) : RingHom.ker (psi k) = Pk k := by sorry
