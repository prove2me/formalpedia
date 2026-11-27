-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ker_psi
-- name    : MohP3.FormalLocal.ker_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:29:01.384565+00:00
-- url     : https://prove2.me/theorems/93da1414-665d-4deb-8062-de58d94bfa7b
-- title:
--   Formal Local: ker psi
-- statement:
--   The kernel of the formal parametrization is exactly the curve ideal
--   `Pk = (f1,f2,f3,f4) k[[x,y,z]]`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L547-L548
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L547-L548

module
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_Generation
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries MohP3.Wt
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.FormalLocal.ker_psi (k : Type*) [Field k] [CharZero k] : RingHom.ker (psi k) = Pk k := by sorry
