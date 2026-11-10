-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_phase2_correctness
-- name    : MultiPartyError1146.Adaptive.phase2_correctness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:37.287743+00:00
-- url     : https://prove2.me/theorems/d666b2d2-c902-4eba-81d3-7ad6586e85da
-- title:
--   Lemma 4.6 — exceptional receivers after phase 2
-- statement:
--   At phase-2 end the canonical exceptional receiver set $S_2$ satisfies
--   $$|S_2|\le\sqrt n/4,\qquad x_k^{(i)}=x_k\quad(i\notin S_2,\ k\notin S_1).$$
--   The local view here includes the supermajority conversion, so unsure counts as incorrect. This is the complete two-set statement needed by phase 3.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths and sufficiently large n → ceiling-rounded widths, speaker prefixes and lengths, with a uniform large-n threshold; reason: the asymptotic scheduling convention is made integral; exact numerical correctness thresholds are retained
--   - encoding: fixed codes, selectors, input and small-budget execution in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - encoding: sufficiently small c depending on η and fixed code rates → for every positive iteration count R and rate coefficient a≥1, c>0 and a size threshold are chosen before n, codes, inputs and noise; reason: this exposes the standing uniformity and identifies η=1/(2R) internally
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
--   - encoding: existence of exceptional sets, chosen canonically in the proof → the canonical sets of coordinates or receivers defined by actual errors; reason: the proof specifies these sets and proves their bounds, including unsure as incorrect
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 4.6, printed p.23, PDF p.25

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem phase2_correctness :
    ∀ R : ℕ, 1 ≤ R → ∀ a : ℝ, 1 ≤ a → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : AlgorithmData n R,
        D.Good a → ∀ (x : Input n 1) (A : Adversary n (duration D)),
          averageError (algorithm1 D) x A ≤ c / Real.sqrt n →
          ((exceptionalReceivers D x A).card : ℝ) ≤ Real.sqrt n / 4 ∧
          ∀ i, i ∉ exceptionalReceivers D x A → ∀ k, k ∉ exceptionalInputs D x A →
            (snapshot D x A (phase2Time D) i).view k = some (x k 0) := by sorry

end MultiPartyError1146.Adaptive
