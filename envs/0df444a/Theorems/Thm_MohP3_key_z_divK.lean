-- Prove2me | Theorems.Thm_MohP3_key_z_divK
-- name    : MohP3.key_z_divK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:03:14.278125+00:00
-- url     : https://prove2.me/theorems/1e0a6607-b36c-525a-bb93-0cbca121ec5c
-- title:
--   Moh P3: key z div K
-- statement:
--   The Moh P3 construction uses the key z div K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L138-L146
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/GlobalK.lean#L138-L146

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

theorem MohP3.key_z_divK (i : Fin 8) :
    zk k * hhK k i = MvPolynomial.C ((18 : k)⁻¹) *
      ((∑ j, Gen.qzA (yk k) i j * hhK k j) +
        ∑ j, Gen.wzA (xk k) (yk k) (zk k) i j * ffK k j) := by sorry
