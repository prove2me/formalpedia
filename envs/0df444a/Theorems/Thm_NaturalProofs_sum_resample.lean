-- Prove2me | Theorems.Thm_NaturalProofs_sum_resample
-- name    : NaturalProofs.sum_resample
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:00.767787+00:00
-- url     : https://prove2.me/theorems/05076a25-b509-4522-a1ae-9002244a6f28
-- title:
--   Natural Proofs: sum resample
-- statement:
--   Resampling one coordinate of a uniformly random function keeps it uniform.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L86-L100
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L86-L100

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

theorem NaturalProofs.sum_resample [DecidableEq I] (e : I) (h : (I → X) → ℝ) :
    ∑ ω : I → X, ∑ z : X, h (Function.update ω e z) = Fintype.card X * ∑ ω, h ω := by sorry
