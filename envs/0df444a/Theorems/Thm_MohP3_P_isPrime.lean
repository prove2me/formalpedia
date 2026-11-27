-- Prove2me | Theorems.Thm_MohP3_P_isPrime
-- name    : MohP3.P_isPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T21:56:57.583428+00:00
-- url     : https://prove2.me/theorems/ab0aca24-0e8c-5b48-b9e7-c9969fbed9ed
-- title:
--   Moh P3: P is Prime
-- statement:
--   `P` is a prime ideal: it is the kernel of a map to the integral domain
--   `ℚ[t]`.
--
--   Source: https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Global.lean#L23-L23
-- source:
--   https://github.com/GrgAakash/moh-p3-set-theoretic-complete-intersection/blob/abbdac729c91a6c7784a3dd15ff6828f2ce6e7fc/MohP3/Global.lean#L23-L23

module
public import Definitions.Def_MohP3_Kernel
public import Definitions.Def_MohP3_Global
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MvPolynomial
open MohP3

theorem MohP3.P_isPrime : P.IsPrime := by sorry
