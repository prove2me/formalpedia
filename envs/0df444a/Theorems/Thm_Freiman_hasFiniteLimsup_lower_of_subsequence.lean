-- Prove2me | Theorems.Thm_Freiman_hasFiniteLimsup_lower_of_subsequence
-- name    : Freiman.hasFiniteLimsup_lower_of_subsequence
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T10:53:31.199723+00:00
-- url     : https://prove2.me/theorems/00f144e5-1f82-4665-9573-aa77412204ad
-- title:
--   hasFiniteLimsup lower of subsequence
-- statement:
--   A real sequence with a strictly increasing subsequence converging to $t$ satisfies the lower epsilon condition in the existing HasFiniteLimsup definition.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, §1.6, Theorem 1.9 (found:separated-peaks), proof by separated copies.

import Definitions.Def_Freiman_wordRealization
import Mathlib.Topology.Instances.Real.Lemmas

open Freiman

theorem Freiman.hasFiniteLimsup_lower_of_subsequence (v : ℕ → ℝ) (t : ℝ) (p : ℕ → ℕ)
    (hp : StrictMono p) (hlim : Filter.Tendsto (fun j : ℕ => v (p j)) Filter.atTop (nhds t)) :
    ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ t - ε < v n := by sorry
