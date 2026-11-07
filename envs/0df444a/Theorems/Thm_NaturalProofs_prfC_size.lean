-- Prove2me | Theorems.Thm_NaturalProofs_prfC_size
-- name    : NaturalProofs.prfC_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T08:34:01.314901+00:00
-- url     : https://prove2.me/theorems/ab044b31-1483-4069-a384-06b9dd2308d0
-- title:
--   Natural Proofs: prf C size
-- statement:
--   The Natural Proofs construction uses the prf C size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L276-L279
-- source:
--   https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/NaturalProofs/GGM.lean#L276-L279

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
variable {β : Type} (gc : (k : ℕ) → Fin (2 * k) → Circuit (Fin k))

theorem NaturalProofs.prfC_size {k B : ℕ} (hB : ∀ j, (gc k j).size ≤ B) (hk : 0 < k) (n : ℕ) (s : Bits k) :
    (prfC gc hk n s).size ≤ n * (2 * k * B + 4 * k) := by sorry
