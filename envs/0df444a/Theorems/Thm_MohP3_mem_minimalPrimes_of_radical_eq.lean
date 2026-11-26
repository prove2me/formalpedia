-- Prove2me | Theorems.Thm_MohP3_mem_minimalPrimes_of_radical_eq
-- name    : MohP3.mem_minimalPrimes_of_radical_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:02:50.591097+00:00
-- url     : https://prove2.me/theorems/f0dded25-3e7b-4f50-9e85-fe67b696c26c
-- title:
--   Moh P3: mem minimal Primes of radical eq
-- statement:
--   If the radical of `I` is a prime ideal `p`, then `p` is a minimal prime
--   of `I`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean#L46-L50
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Ara.lean#L46-L50

module
public import Mathlib
public import Definitions.Def_MohP3_Ara
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MohP3
variable {A : Type*} [CommRing A]

theorem MohP3.mem_minimalPrimes_of_radical_eq {I p : Ideal A} (hp : p.IsPrime)
    (h : I.radical = p) : p ∈ I.minimalPrimes := by sorry
