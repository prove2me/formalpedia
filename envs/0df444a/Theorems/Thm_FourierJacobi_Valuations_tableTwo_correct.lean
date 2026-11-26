-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_tableTwo_correct
-- name    : FourierJacobi.Valuations.tableTwo_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:24.449232+00:00
-- url     : https://prove2.me/theorems/b19d5094-1c20-4fe9-b073-a348d47571fe
-- title:
--   Valuations: table Two correct
-- statement:
--   The Valuations construction uses the table Two correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L106-L111
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L106-L111

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
set_option maxHeartbeats 2000000

theorem FourierJacobi.Valuations.tableTwo_correct (k j h c : ℤ) (hc : 0 ≤ c) :
    tableTwo k j h c = cartanIndices 2 k j h c := by sorry
