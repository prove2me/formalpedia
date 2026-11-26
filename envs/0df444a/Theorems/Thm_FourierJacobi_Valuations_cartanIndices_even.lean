-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_cartanIndices_even
-- name    : FourierJacobi.Valuations.cartanIndices_even
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:20:32.143675+00:00
-- url     : https://prove2.me/theorems/5f5bef5d-312c-49f4-a420-1852e109b232
-- title:
--   Valuations: cartan Indices even
-- statement:
--   The Valuations construction uses the cartan Indices even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L126-L129
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L126-L129

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations

theorem FourierJacobi.Valuations.cartanIndices_even (r k j h c : ℤ) : Even (cartanIndices r k j h c).1 := by sorry
