-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_strong_lead
-- name    : MultiPartyError1146.Adaptive.strong_lead
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:36:16.559565+00:00
-- url     : https://prove2.me/theorems/24b6ec95-ceaf-40f9-9e76-245999dd4856
-- title:
--   Lemma 4.5 — correct vote lead duration
-- statement:
--   For every iteration and every $k\notin S_1$, the actual duration vote at iteration end satisfies
--   $$(-1)^{1-x_k}\xi_k^*>\tfrac34N_r.$$
--   The true counter uses $L/90$, with positive and negative crossings counted with their signs. The result is simultaneous over iterations, to be established together with phase-2 correctness by induction.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths and sufficiently large n → ceiling-rounded widths, speaker prefixes and lengths, with a uniform large-n threshold; reason: the asymptotic scheduling convention is made integral; exact numerical correctness thresholds are retained
--   - encoding: fixed codes, selectors, input and small-budget execution in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - encoding: sufficiently small c depending on η and fixed code rates → for every positive iteration count R and rate coefficient a≥1, c>0 and a size threshold are chosen before n, codes, inputs and noise; reason: this exposes the standing uniformity and identifies η=1/(2R) internally
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 4.5, printed p.22, PDF p.24

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem strong_lead :
    ∀ R : ℕ, 1 ≤ R → ∀ a : ℝ, 1 ≤ a → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : AlgorithmData n R,
        D.Good a → ∀ (x : Input n 1) (A : Adversary n (duration D)),
          averageError (algorithm1 D) x A ≤ c / Real.sqrt n →
          ∀ (r : Fin R) (k : Fin n), k ∉ exceptionalInputs D x A →
            (3 : ℝ) / 4 * prefixSize n R r.val <
              (sign (x k 0) * trueXi D x A r k : ℤ) := by sorry

end MultiPartyError1146.Adaptive
