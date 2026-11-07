-- Prove2me | Theorems.Thm_NaturalProofs_exists_abs_ge_avg
-- name    : NaturalProofs.exists_abs_ge_avg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:35.851986+00:00
-- url     : https://prove2.me/theorems/c4b46df4-2dc1-461d-8729-419daf2b7e4f
-- title:
--   Natural Proofs: exists abs ge avg
-- statement:
--   Some term is at least the average in absolute value.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L74-L83
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L74-L83

module
public import Mathlib
public import Definitions.Def_NaturalProofs_Prob
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]

theorem NaturalProofs.exists_abs_ge_avg [Nonempty Ω] (u : Ω → ℝ) :
    ∃ ω, |∑ ω, u ω| / Fintype.card Ω ≤ |u ω| := by sorry
