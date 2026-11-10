-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_phase2_induction
-- name    : MultiPartyError1146.Adaptive.phase2_induction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:41.449925+00:00
-- url     : https://prove2.me/theorems/d1a222e3-3277-4afc-a051-ca37a246b926
-- title:
--   Lemma 4.4 — correctness among next speakers
-- statement:
--   At the end of each iteration $r$, every $k\notin S_1$ is estimated correctly by strictly more than $99/100$ of the next speaker prefix:
--   $$|\{i\le N_{r+1}:x_k^{(i)}=x_k\}|>99N_{r+1}/100.$$
--   The estimate is taken before the final supermajority conversion, retained explicitly in the local state. The last iteration is included. This and the strong-lead/accounting assertions form a simultaneous induction, without assuming the current conclusion.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths and sufficiently large n → ceiling-rounded widths, speaker prefixes and lengths, with a uniform large-n threshold; reason: the asymptotic scheduling convention is made integral; exact numerical correctness thresholds are retained
--   - encoding: fixed codes, selectors, input and small-budget execution in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - encoding: sufficiently small c depending on η and fixed code rates → for every positive iteration count R and rate coefficient a≥1, c>0 and a size threshold are chosen before n, codes, inputs and noise; reason: this exposes the standing uniformity and identifies η=1/(2R) internally
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Lemma 4.4, printed p.22, PDF p.24

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem phase2_induction :
    ∀ R : ℕ, 1 ≤ R → ∀ a : ℝ, 1 ≤ a → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
      ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ D : AlgorithmData n R,
        D.Good a → ∀ (x : Input n 1) (A : Adversary n (duration D)),
          averageError (algorithm1 D) x A ≤ c / Real.sqrt n →
          ∀ (r : Fin R) (k : Fin n), k ∉ exceptionalInputs D x A →
            (99 : ℝ) / 100 * prefixSize n R (r.val + 1) <
              ((Finset.univ.filter fun i => i.val < prefixSize n R (r.val + 1) ∧
                (snapshot D x A (iterationEnd D r.val) i).estimate k = x k 0).card : ℝ) := by sorry

end MultiPartyError1146.Adaptive
