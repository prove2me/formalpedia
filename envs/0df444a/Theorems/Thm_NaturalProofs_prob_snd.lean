-- Prove2me | Theorems.Thm_NaturalProofs_prob_snd
-- name    : NaturalProofs.prob_snd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:27:17.766405+00:00
-- url     : https://prove2.me/theorems/dda18de2-c098-40ce-855a-56e48ec2d541
-- title:
--   Natural Proofs: prob snd
-- statement:
--   The Natural Proofs construction uses the prob snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L52-L56
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/Prob.lean#L52-L56

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

theorem NaturalProofs.prob_snd [Nonempty A] (p : B → Bool) : prob (fun ω : A × B => p ω.2) = prob p := by sorry
