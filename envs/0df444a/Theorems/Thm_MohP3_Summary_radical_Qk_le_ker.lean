-- Prove2me | Theorems.Thm_MohP3_Summary_radical_Qk_le_ker
-- name    : MohP3.Summary.radical_Qk_le_ker
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:43:24.651205+00:00
-- url     : https://prove2.me/theorems/0fe5a9ed-4d6e-524e-a53d-60d6e3e7b869
-- title:
--   Summary: radical Qk le ker
-- statement:
--   Over `k[[x,y,z]]`, one inclusion of the formal-local statement holds
--   unconditionally.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L139-L141
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L139-L141

module
public import Definitions.Def_MohP3_Defs
public import Definitions.Def_MohP3_Certificate
public import Definitions.Def_MohP3_Independence
public import Definitions.Def_MohP3_Closure
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_FormalLocal
public import Definitions.Def_MohP3_Order
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_Generation
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
public import Definitions.Def_MohP3_MvPowerSeriesAux
public import Definitions.Def_MohP3_HeightLocal
public import Definitions.Def_MohP3_HeightK
public import Definitions.Def_MohP3_HilbertBurch
public import Definitions.Def_MohP3
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_le_ker

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
open MohP3.FormalLocal

theorem MohP3.Summary.radical_Qk_le_ker (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical ≤ RingHom.ker (psi k) := by sorry
