-- Prove2me | Theorems.Thm_NaturalProofs_expand_pre
-- name    : NaturalProofs.expand_pre
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:28:30.882038+00:00
-- url     : https://prove2.me/theorems/febdfd15-aee0-4ba0-bb5f-c80200c9d116
-- title:
--   Natural Proofs: expand pre
-- statement:
--   The Natural Proofs construction uses the expand pre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L73-L76
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L73-L76

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

theorem NaturalProofs.expand_pre {k n : ℕ} (i : ℕ) (M : (Fin i → Bool) → Fin (2 * k) → Bool)
    (x : Fin n → Bool) :
    expand M (pre (i + 1) x) = half ((List.ofFn x).getD i false) (M (pre i x)) := by sorry
