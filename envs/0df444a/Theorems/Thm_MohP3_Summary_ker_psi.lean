-- Prove2me | Theorems.Thm_MohP3_Summary_ker_psi
-- name    : MohP3.Summary.ker_psi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:39:23.994163+00:00
-- url     : https://prove2.me/theorems/4157c3ed-b2eb-55f6-b340-b95db1f1e277
-- title:
--   Summary: ker psi
-- statement:
--   The kernel of the formal parametrization, unconditionally.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L163-L164
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3.lean#L163-L164

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
public import Theorems.Thm_MohP3_FormalLocal_ker_psi

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3 MohP3.Summary
open MohP3.FormalLocal

theorem MohP3.Summary.ker_psi (k : Type*) [Field k] [CharZero k] : RingHom.ker (psi k) = Pk k := by sorry
