-- Prove2me | Theorems.Thm_MohP3_FormalLocal_iter_telescope
-- name    : MohP3.FormalLocal.iter_telescope
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:30:33.269552+00:00
-- url     : https://prove2.me/theorems/086019b8-9e82-4ed5-ac43-19b2decf2fc9
-- title:
--   Formal Local: iter telescope
-- statement:
--   The Formal Local construction uses the iter telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L492-L504
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Generation.lean#L492-L504

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

theorem MohP3.FormalLocal.iter_telescope (F : Sk k) (M : ℕ) :
    F - (iter k F M).1 =
      (∑ i, iotaS k (∑ s ∈ Finset.range M, (iter k F (s + 1)).2.1 i) * hhS k i) +
        ∑ j, (∑ s ∈ Finset.range M, (iter k F (s + 1)).2.2 j) * ffS k j := by sorry
