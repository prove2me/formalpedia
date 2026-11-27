-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ffS_eq
-- name    : MohP3.FormalLocal.ffS_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:32:10.801619+00:00
-- url     : https://prove2.me/theorems/afb64640-5ffa-5199-b036-55f0a6f303d7
-- title:
--   Formal Local: ff S eq
-- statement:
--   The Formal Local construction uses the ff S eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L56-L56
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L56-L56

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

theorem MohP3.FormalLocal.ffS_eq (j : Fin 4) : ffS k j = Gen.ff (xs k) (ys k) (zs k) j := by sorry
