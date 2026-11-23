-- Prove2me | Theorems.Thm_KernelRank_injective_rates_with_conjugates
-- name    : KernelRank.injective_rates_with_conjugates
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:01:30.85172+00:00
-- url     : https://prove2.me/theorems/98d86504-98d6-4aa0-8271-1a13153288d9
-- title:
--   Kernel Rank: injective rates with conjugates
-- statement:
--   Adjoining the conjugates of upper-half-plane rates introduces no duplicate rates.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L45-L58
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/RealExpPoly.lean#L45-L58

import Definitions.Def_KernelRankLean_ExpPoly
import Definitions.Def_KernelRankLean_RealExpPoly
set_option autoImplicit true
open Complex Polynomial
open KernelRank

theorem KernelRank.injective_rates_with_conjugates {ι : Type*} {rate : ι → ℂ}
    (hinj : Function.Injective rate) (hup : ∀ i, 0 ≤ (rate i).im) :
    Function.Injective
      (Sum.elim rate (fun j : {i // 0 < (rate i).im} => starRingEnd ℂ (rate j.1))) := by sorry
