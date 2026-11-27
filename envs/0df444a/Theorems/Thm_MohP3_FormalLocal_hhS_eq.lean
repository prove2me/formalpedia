-- Prove2me | Theorems.Thm_MohP3_FormalLocal_hhS_eq
-- name    : MohP3.FormalLocal.hhS_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:31:56.562051+00:00
-- url     : https://prove2.me/theorems/8343bef5-8339-5680-8765-f382385e03e0
-- title:
--   Formal Local: hh S eq
-- statement:
--   The Formal Local construction uses the hh S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L53-L53
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L53-L53

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
omit [CharZero k]

theorem MohP3.FormalLocal.hhS_eq (i : Fin 8) : hhS k i = Gen.hh (xs k) (ys k) (zs k) i := by sorry
