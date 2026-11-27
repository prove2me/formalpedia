-- Prove2me | Theorems.Thm_MohP3_Summary_radical_Qk_eq_radical_Pk
-- name    : MohP3.Summary.radical_Qk_eq_radical_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:43:59.258717+00:00
-- url     : https://prove2.me/theorems/426d3e5b-c61c-4a89-b47d-9f181c34cf7a
-- title:
--   Summary: radical Qk eq radical Pk
-- statement:
--   Over `k[[x,y,z]]`, the two ideals have the same radical, unconditionally.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L145-L147
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L145-L147

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
public import Theorems.Thm_MohP3_FormalLocal_radical_Qk_eq_radical_Pk

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
open MohP3.FormalLocal

theorem MohP3.Summary.radical_Qk_eq_radical_Pk (k : Type*) [Field k] [CharZero k] :
    (Qk k).radical = (Pk k).radical := by sorry
