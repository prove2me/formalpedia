-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_phase1_correctness
-- name    : MultiPartyError1146.Adaptive.phase1_correctness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:34.536207+00:00
-- url     : https://prove2.me/theorems/08a39f56-e9f1-4c5f-915f-ac7d1e6e48b9
-- title:
--   Lemma 4.3 — phase-1 correctness
-- statement:
--   Fix the code-rate coefficient and internal iteration count. A sufficiently small positive constant $c$, uniform in all later sizes and executions, ensures that after phase 1 the canonical exceptional set $S_1$ satisfies
--   $$|S_1|\le\sqrt n/4,$$
--   and every $k\notin S_1$ is estimated correctly by strictly more than $99n/100$ parties. This establishes the base for phase-2 induction.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths and sufficiently large n → ceiling-rounded widths, speaker prefixes and lengths, with a uniform large-n threshold; reason: the asymptotic scheduling convention is made integral; exact numerical correctness thresholds are retained
--   - encoding: fixed codes, selectors, input and small-budget execution in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - encoding: sufficiently small c depending on η and fixed code rates → for every positive iteration count R and rate coefficient a≥1, c>0 and a size threshold are chosen before n, codes, inputs and noise; reason: this exposes the standing uniformity and identifies η=1/(2R) internally
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
--   - encoding: existence of exceptional sets, chosen canonically in the proof → the canonical sets of coordinates or receivers defined by actual errors; reason: the proof specifies these sets and proves their bounds, including unsure as incorrect
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 4.3, printed p.22, PDF p.24

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem phase1_correctness :
    ∀ R : ℕ, 1 ≤ R → ∀ a : ℝ, 1 ≤ a → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : AlgorithmData n R,
        D.Good a → ∀ (x : Input n 1) (A : Adversary n (duration D)),
          averageError (algorithm1 D) x A ≤ c / Real.sqrt n →
          ((exceptionalInputs D x A).card : ℝ) ≤ Real.sqrt n / 4 ∧
          ∀ k, k ∉ exceptionalInputs D x A →
            (99 : ℝ) / 100 * n <
              ((Finset.univ.filter fun i => (snapshot D x A (phase1Time D) i).estimate k = x k 0).card : ℝ) := by sorry

end MultiPartyError1146.Adaptive
