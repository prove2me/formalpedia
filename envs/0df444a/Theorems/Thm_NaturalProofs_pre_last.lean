-- Prove2me | Theorems.Thm_NaturalProofs_pre_last
-- name    : NaturalProofs.pre_last
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:32:44.693546+00:00
-- url     : https://prove2.me/theorems/3e6e352c-9e1b-4a7e-823f-edb23c9a2f6f
-- title:
--   Natural Proofs: pre last
-- statement:
--   The Natural Proofs construction uses the pre last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L69-L71
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L69-L71

module
public import Definitions.Def_NaturalProofs_Circuits
public import Definitions.Def_NaturalProofs_Prob
public import Definitions.Def_NaturalProofs_GGM
set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open MCircuit
variable (G : (k : ℕ) → (Fin k → Bool) → Fin (2 * k) → Bool)

theorem NaturalProofs.pre_last {n : ℕ} (i : ℕ) (x : Fin n → Bool) :
    pre (i + 1) x (Fin.last i) = (List.ofFn x).getD i false := by sorry
