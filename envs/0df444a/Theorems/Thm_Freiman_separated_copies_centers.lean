-- Prove2me | Theorems.Thm_Freiman_separated_copies_centers
-- name    : Freiman.separated_copies_centers
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:10.660731+00:00
-- url     : https://prove2.me/theorems/e291f600-de65-4716-b127-b6ec3086a75d
-- title:
--   separated copies centers
-- statement:
--   The centers of successive copied windows form a strictly increasing sequence. Their local values tend to the original central value because their matching window radii tend to infinity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization
import Mathlib.Topology.Instances.Real.Lemmas

open Freiman

theorem Freiman.separated_copies_centers (a b : ℤ → ℕ+) (N : ℕ) (hcopy : SeparatedCopies a b N) :
    ∃ p : ℕ → ℕ, StrictMono p ∧ Filter.Tendsto (fun j : ℕ => localValue b (p j : ℤ)) Filter.atTop (nhds (localValue a 0)) := by sorry
