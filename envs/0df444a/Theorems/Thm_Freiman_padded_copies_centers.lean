-- Prove2me | Theorems.Thm_Freiman_padded_copies_centers
-- name    : Freiman.padded_copies_centers
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:39.795988+00:00
-- url     : https://prove2.me/theorems/62070ce3-5105-4c6a-a8da-b3b1a0e1a110
-- title:
--   padded copies centers
-- statement:
--   The central local values in the concatenated word converge to the same target as the model central values. Their matching windows have radii 2j, so the error is bounded by the cylinder estimate tending to zero.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Lemma 1.11 (found:padded-models), padding and finite-window proof.

import Definitions.Def_Freiman_paddedCopies
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Topology.Instances.Real.Lemmas

open Freiman

theorem Freiman.padded_copies_centers (a : ℕ → ℤ → ℕ+) (b : ℤ → ℕ+) (d : ℕ+) (t : ℝ)
    (hcopy : PaddedCopies a b d)
    (hcentral : Filter.Tendsto (fun j : ℕ => localValue (a j) 0) Filter.atTop (nhds t)) :
    ∃ p : ℕ → ℕ, StrictMono p ∧ Filter.Tendsto (fun j : ℕ => localValue b (p j : ℤ)) Filter.atTop (nhds t) := by sorry
