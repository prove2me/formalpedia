-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ker_le_Pk_of_generation
-- name    : MohP3.FormalLocal.ker_le_Pk_of_generation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:58:12.070461+00:00
-- url     : https://prove2.me/theorems/3f88e016-692f-43b7-ac6a-cd13d9b02a2f
-- title:
--   Formal Local: ker le Pk of generation
-- statement:
--   Granting the completed generation statement, the kernel of the formal
--   parametrization is exactly `Pk`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L318-L330
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L318-L330

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

theorem MohP3.FormalLocal.ker_le_Pk_of_generation (hgen : Generation k) : RingHom.ker (psi k) ≤ Pk k := by sorry
