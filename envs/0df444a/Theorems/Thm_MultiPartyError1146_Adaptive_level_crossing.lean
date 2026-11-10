-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_level_crossing
-- name    : MultiPartyError1146.Adaptive.level_crossing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:49.078184+00:00
-- url     : https://prove2.me/theorems/30c1cf07-b185-4d5f-8b8a-3213b48e3d0a
-- title:
--   Claim 4.7 — level crossings of F
-- statement:
--   In any iteration, let $N_r$ be its number of speakers and let $\tau\in[-N_r,N_r]$ be an integer level. For every coordinate $k\notin S_1$,
--   $$F(\tau)\le\mathbf1_{\tau>0}+|E'_{k,\tau}|+|E'_{k,\tau-1}|.$$
--   All terms use actual broadcasts and the post-broadcast signed vote. The inequality isolates the incorrect-speaker contribution to repeated crossings. The statement also covers arbitrary received-symbol matrices at every positive size; no global corruption-budget premise is needed.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths → ceiling-rounded widths, speaker prefixes and lengths; reason: finite schedules implement the asymptotic pseudocode; exact numerical correctness thresholds are retained
--   - encoding: fixed codes and selectors in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - generalization: sufficiently large n and the fixed small-budget execution in the surrounding induction setting → every positive n and every input and received-symbol matrix, without a global corruption-budget or induction premise, retaining k outside S1; reason: the level-crossing argument uses only frozen estimates and unit signed increments, so it applies without any budget or large-size estimate and specializes to the source execution
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Claim 4.7, printed p.26, PDF p.28

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem level_crossing (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (a : ℝ)
    (D : AlgorithmData n R) (hD : D.Good a) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n)
    (hk_good : k ∉ exceptionalInputs D x A)
    (τ : ℤ) (hτ : -(prefixSize n R r.val : ℤ) ≤ τ ∧ τ ≤ prefixSize n R r.val) :
    Fcount D x A r k (· = τ) ≤ (if 0 < τ then 1 else 0) +
      (wrongAtLevel D x A r k τ).card + (wrongAtLevel D x A r k (τ - 1)).card := by sorry

end MultiPartyError1146.Adaptive
