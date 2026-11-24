-- Prove2me | Theorems.Thm_InverseZeroSum_Candidate3_eta17Input
-- name    : InverseZeroSum.Candidate3.eta17Input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T05:29:10.016569+00:00
-- url     : https://prove2.me/theorems/44a0f48b-6cd4-4068-9917-9329971fe591
-- title:
--   Candidate3: eta17 Input
-- statement:
--   Kernel-checked realization of the exact ordinary eta(C_3^3)=17 source
--   interface.  A hypothetical short-free length-17 sequence has support which is
--   a cap.  Since it also has no two-term zero sum, adjoining the origin preserves
--   the cap property; S045's cap bound then forces support size at most eight.
--   Every support value has multiplicity at most two, contradicting 17 positions.
--
--   Source: https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L853-L1017
-- source:
--   https://github.com/jfairfaxball-348/Inverse-Zero-Sum-Research/blob/c5f9e5e822020688c72b2a3bfacbf147a801e219/InverseZeroSum/Candidate3.lean#L853-L1017

module
public import Mathlib
public import Definitions.Def_InverseZeroSum_Candidate3
set_option autoImplicit true
@[expose] public section
public section
open InverseZeroSum InverseZeroSum.Candidate3

theorem InverseZeroSum.Candidate3.eta17Input : Eta17Input := by sorry
