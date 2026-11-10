-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_aggregate_wrong_bound
-- name    : MultiPartyError1146.Adaptive.aggregate_wrong_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:50.588612+00:00
-- url     : https://prove2.me/theorems/33df6a63-da26-44b7-9795-a3a88e712f56
-- title:
--   Claim 4.12 — aggregate incorrect estimates
-- statement:
--   In the uniform small-budget setup, a single positive coefficient $B$ bounds the aggregate initially incorrect estimates in every iteration:
--   $$\sum_{k'\ne k}|E'_{k'}|\le B n^{3/2}\qquad(k\notin S_1).$$
--   The assertion is simultaneous over iterations. Its proof belongs to the same induction as Lemmas 4.4 and 4.5; no correctness hypothesis from the current iteration, or error-accounting conclusion, is added to the statement.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths and sufficiently large n → ceiling-rounded widths, speaker prefixes and lengths, with a uniform large-n threshold; reason: the asymptotic scheduling convention is made integral; exact numerical correctness thresholds are retained
--   - encoding: fixed codes, selectors, input and small-budget execution in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - encoding: sufficiently small c depending on η and fixed code rates → for every positive iteration count R and rate coefficient a≥1, c>0 and a size threshold are chosen before n, codes, inputs and noise; reason: this exposes the standing uniformity and identifies η=1/(2R) internally
--   - encoding: O(n^(3/2)) in the induction proof → one uniform B and simultaneous quantification over all iterations; reason: the induction and its accounting refinement are proof obligations, not assumed invariants
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Claim 4.12, printed p.28, PDF p.30

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem aggregate_wrong_bound :
    ∀ R : ℕ, 1 ≤ R → ∀ a : ℝ, 1 ≤ a → ∃ c B : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < B ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : AlgorithmData n R,
        D.Good a → ∀ (x : Input n 1) (A : Adversary n (duration D)),
          averageError (algorithm1 D) x A ≤ c / Real.sqrt n →
          ∀ (r : Fin R) (k : Fin n), k ∉ exceptionalInputs D x A →
            (otherWrongCount D x A r k : ℝ) ≤ B * (n : ℝ) ^ ((3 : ℝ) / 2) := by sorry

end MultiPartyError1146.Adaptive
