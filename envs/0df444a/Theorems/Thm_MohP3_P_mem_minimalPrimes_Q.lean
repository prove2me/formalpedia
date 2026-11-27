-- Prove2me | Theorems.Thm_MohP3_P_mem_minimalPrimes_Q
-- name    : MohP3.P_mem_minimalPrimes_Q
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T22:04:48.879741+00:00
-- url     : https://prove2.me/theorems/d36a3df7-327f-4ff3-ab8c-8cfd33e9a11d
-- title:
--   Moh P3: P mem minimal Primes Q
-- statement:
--   `P` is a minimal prime of `Q`: indeed `Q.radical = P`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L41-L42
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Height.lean#L41-L42

module
public import Definitions.Def_MohP3_Global
public import Definitions.Def_MohP3_Ara
public import Definitions.Def_MohP3_Height
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.P_mem_minimalPrimes_Q : P ∈ Q.minimalPrimes := by sorry
