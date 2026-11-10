-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_total_decoding_bound
-- name    : MultiPartyError1146.Adaptive.total_decoding_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:42.968328+00:00
-- url     : https://prove2.me/theorems/c352912f-43cf-4e0b-a33a-4604dd87802e
-- title:
--   Claim 4.11 — total incorrectly decoded messages
-- statement:
--   With the uniform small-budget setup, there is a coefficient $B>0$, chosen before all sizes, code data and executions, for which every iteration satisfies
--   $$\sum_{i\le N_r}|E_i|\le B n^{2+h}/L_r,\qquad h=1/(2R).$$
--   This makes the source's uniform $O(n^{2+\eta}/L_r)$ statement explicit, rather than choosing a constant separately for each execution.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths and sufficiently large n → ceiling-rounded widths, speaker prefixes and lengths, with a uniform large-n threshold; reason: the asymptotic scheduling convention is made integral; exact numerical correctness thresholds are retained
--   - encoding: fixed codes, selectors, input and small-budget execution in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - encoding: sufficiently small c depending on η and fixed code rates → for every positive iteration count R and rate coefficient a≥1, c>0 and a size threshold are chosen before n, codes, inputs and noise; reason: this exposes the standing uniformity and identifies η=1/(2R) internally
--   - encoding: O(n^(2+η)/Lr) → a single positive B before n, codes, inputs and noise; reason: the standing asymptotic constant is exposed
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Claim 4.11, printed p.28, PDF p.30

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem total_decoding_bound :
    ∀ R : ℕ, 1 ≤ R → ∀ a : ℝ, 1 ≤ a → ∃ c B : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < B ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : AlgorithmData n R,
        D.Good a → ∀ (x : Input n 1) (A : Adversary n (duration D)),
          averageError (algorithm1 D) x A ≤ c / Real.sqrt n →
          ∀ r : Fin R, (totalDecodingErrors D x A r : ℝ) ≤
            B * (n : ℝ) ^ (2 + exponent R) / width n R r.val := by sorry

end MultiPartyError1146.Adaptive
