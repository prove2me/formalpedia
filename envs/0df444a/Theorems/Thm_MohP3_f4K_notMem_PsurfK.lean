-- Prove2me | Theorems.Thm_MohP3_f4K_notMem_PsurfK
-- name    : MohP3.f4K_notMem_PsurfK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:07:25.688818+00:00
-- url     : https://prove2.me/theorems/d26d1558-14fc-40bf-8f23-7e2f5b25160c
-- title:
--   Moh P3: f4 K not Mem Psurf K
-- statement:
--   `f4` vanishes on the curve but not on the surface.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L107-L115
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightK.lean#L107-L115

module
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_HeightK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]
omit [CharZero k]

theorem MohP3.f4K_notMem_PsurfK : Gen.f4 (xk k) (yk k) (zk k) ∉ PsurfK k := by sorry
