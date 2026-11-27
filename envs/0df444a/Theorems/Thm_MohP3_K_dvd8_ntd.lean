-- Prove2me | Theorems.Thm_MohP3_K_dvd8_ntd
-- name    : MohP3.K.dvd8_ntd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:01:34.20601+00:00
-- url     : https://prove2.me/theorems/87cb34ed-ecf2-5d56-a816-81dd2a89e039
-- title:
--   K: dvd8 ntd
-- statement:
--   The K construction uses the dvd8 ntd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L52-L55
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/IndependenceK.lean#L52-L55

module
public import Mathlib
public import Definitions.Def_MohP3_IndependenceK
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Polynomial
open MohP3 MohP3.K
variable (k : Type*) [Field k]
variable {k}

theorem MohP3.K.dvd8_ntd {p : Polynomial k} (hp : p ≠ 0) : 8 ∣ (p.comp (X ^ 8)).natTrailingDegree := by sorry
