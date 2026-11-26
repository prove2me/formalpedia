-- Prove2me | Theorems.Thm_MohP3_key_x_divK
-- name    : MohP3.key_x_divK
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T22:03:28.902453+00:00
-- url     : https://prove2.me/theorems/12abb48f-db68-4ad3-a32d-236602cbc251
-- title:
--   Moh P3: key x div K
-- statement:
--   The Moh P3 construction uses the key x div K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L128-L136
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L128-L136

module
public import Definitions.Def_MohP3_GenClosure
public import Definitions.Def_MohP3_IndependenceK
public import Definitions.Def_MohP3_GlobalK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3
variable (k : Type*) [Field k] [CharZero k]

theorem MohP3.key_x_divK (i : Fin 8) :
    xk k * hhK k i = MvPolynomial.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qxA (yk k) i j * hhK k j) +
        ∑ j, Gen.wxA (xk k) (yk k) (zk k) i j * ffK k j) := by sorry
