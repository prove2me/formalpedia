-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_entry_minor_bounds
-- name    : FourierJacobi.Valuations.entry_minor_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:20.570903+00:00
-- url     : https://prove2.me/theorems/b5b0fe08-b492-49b3-93a8-1e161e6eb09a
-- title:
--   Valuations: entry minor bounds
-- statement:
--   The Valuations construction uses the entry minor bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L113-L117
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L113-L117

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations

theorem FourierJacobi.Valuations.entry_minor_bounds (r k j h c : ℤ) (hc : 0 ≤ c) :
    2 * entryMinimum r k j h ≤ minorMinimum r k j h c ∧
      minorMinimum r k j h c ≤ entryMinimum r k j h := by sorry
