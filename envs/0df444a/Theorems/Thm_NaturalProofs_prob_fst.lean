-- Prove2me | Theorems.Thm_NaturalProofs_prob_fst
-- name    : NaturalProofs.prob_fst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:07.449997+00:00
-- url     : https://prove2.me/theorems/6af980df-e135-42c3-b015-38ca365fdd96
-- title:
--   Natural Proofs: prob fst
-- statement:
--   The Natural Proofs construction uses the prob fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L45-L50
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L45-L50

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

theorem NaturalProofs.prob_fst [Nonempty B] (p : A → Bool) : prob (fun ω : A × B => p ω.1) = prob p := by sorry
