-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_cartanIndices_nonnegative
-- name    : FourierJacobi.Valuations.cartanIndices_nonnegative
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:05:10.916819+00:00
-- url     : https://prove2.me/theorems/25b4bec1-dc6a-4d8a-b5b5-35c67e93422b
-- title:
--   Valuations: cartan Indices nonnegative
-- statement:
--   The Valuations construction uses the cartan Indices nonnegative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L119-L124
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L119-L124

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations

theorem FourierJacobi.Valuations.cartanIndices_nonnegative (r k j h c : ℤ) (hc : 0 ≤ c) :
    0 ≤ (cartanIndices r k j h c).1 ∧ 0 ≤ (cartanIndices r k j h c).2 := by sorry
