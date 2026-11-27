-- Prove2me | Theorems.Thm_MohP3_FormalLocal_arithRank_Pk
-- name    : MohP3.FormalLocal.arithRank_Pk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:02.323892+00:00
-- url     : https://prove2.me/theorems/b8f90122-1b7b-5e1d-b176-648ccc27c81a
-- title:
--   Formal Local: arith Rank Pk
-- statement:
--   **The arithmetic rank of `Pk` is two** as well: the two explicit witnesses
--   `H1, H2` cut out the curve set-theoretically in `k[[x,y,z]]`, and by Krull's
--   height theorem one equation cannot suffice.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L244-L257
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/HeightLocal.lean#L244-L257

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
open scoped Classical

theorem MohP3.FormalLocal.arithRank_Pk : arithRank (Pk k) = 2 := by sorry
