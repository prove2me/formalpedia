-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_tableOne_correct
-- name    : FourierJacobi.Valuations.tableOne_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:19.870418+00:00
-- url     : https://prove2.me/theorems/3c952766-6a3c-5e75-a755-55efb36b48b5
-- title:
--   Valuations: table One correct
-- statement:
--   The Valuations construction uses the table One correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L77-L82
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L77-L82

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations

theorem FourierJacobi.Valuations.tableOne_correct (k j h c : ℤ) (hc : 0 ≤ c) :
    tableOne k j h c = cartanIndices 1 k j h c := by sorry
