-- Prove2me | Theorems.Thm_MohP3_FormalLocal_f4S_notMem_Psurfk
-- name    : MohP3.FormalLocal.f4S_notMem_Psurfk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:27.10332+00:00
-- url     : https://prove2.me/theorems/da3df800-ac62-53d9-a312-f250056fc3dd
-- title:
--   Formal Local: f4 S not Mem Psurfk
-- statement:
--   `f4` does not vanish on the surface `y^5 = z^4`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L201-L212
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L201-L212

module
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPowerSeries
open MohP3 MohP3.FormalLocal
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.FormalLocal.f4S_notMem_Psurfk : Gen.f4 (xs k) (ys k) (zs k) ∉ Psurfk k := by sorry
