-- Prove2me | Theorems.Thm_MohP3_FormalLocal_ooS_mod_inj
-- name    : MohP3.FormalLocal.ooS_mod_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:57:58.597349+00:00
-- url     : https://prove2.me/theorems/140a6412-efc9-4e97-be76-f93ce3ee1681
-- title:
--   Formal Local: oo S mod inj
-- statement:
--   The Formal Local construction uses the oo S mod inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L189-L190
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/FormalLocal.lean#L189-L190

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

theorem MohP3.FormalLocal.ooS_mod_inj {i j : Fin 8} (h : ooS i % 8 = ooS j % 8) : i = j := by sorry
