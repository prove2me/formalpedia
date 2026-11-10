-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_ranking_bound
-- name    : MultiPartyError1146.Adaptive.ranking_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:42.73173+00:00
-- url     : https://prove2.me/theorems/ff61297f-3880-489e-8c37-09995b967caa
-- title:
--   Claim 4.8 — ranking and error bound for G
-- statement:
--   For $k'\ne k$, integer levels $\tau,\tau'\in[-N_r,N_r]$ and $0\le\phi\le N_r$,
--   $$G_{k'}(\le\tau,\tau',\le\phi)\le\mathbf1_{0<\tau'\le1+\tau+4\phi}+|E'_{k',\tau'}|+|E'_{k',\tau'-1}|.$$
--   The five conditions defining $G$ and the before/after-broadcast timing are preserved. This relates least-cushion ranking to the decoding-error allowance. The statement also covers arbitrary received-symbol matrices at every positive size; no global corruption-budget premise is needed.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths → ceiling-rounded widths, speaker prefixes and lengths; reason: finite schedules implement the asymptotic pseudocode; exact numerical correctness thresholds are retained
--   - encoding: fixed codes and selectors in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - generalization: sufficiently large n and the fixed small-budget execution in the surrounding induction setting → every positive n and every input and received-symbol matrix, without a global corruption-budget or induction premise, retaining k outside S1; reason: the ranking argument uses only the least-cushion rule and the actual decoding-error count, so it applies without a global budget or large-size estimate and specializes to the source execution
--   - encoding: integer error-count index φ≥0 → φ : ℕ with casts into signed-level comparisons; reason: the same nonnegative index set is represented
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Claim 4.8, printed p.26, PDF p.28

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem ranking_bound (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (a : ℝ)
    (D : AlgorithmData n R) (hD : D.Good a) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n)
    (hk_good : k ∉ exceptionalInputs D x A)
    (k' : Fin n) (hk : k' ≠ k) (τ τ' : ℤ) (φ : ℕ)
    (hτ : -(prefixSize n R r.val : ℤ) ≤ τ ∧ τ ≤ prefixSize n R r.val)
    (hτ' : -(prefixSize n R r.val : ℤ) ≤ τ' ∧ τ' ≤ prefixSize n R r.val)
    (hφ : φ ≤ prefixSize n R r.val) :
    Gcount D x A r k k' (· ≤ τ) (· = τ') (· ≤ φ) ≤
      (if 0 < τ' ∧ τ' ≤ 1 + τ + 4 * (φ : ℤ) then 1 else 0) +
      (wrongAtLevel D x A r k' τ').card + (wrongAtLevel D x A r k' (τ' - 1)).card := by sorry

end MultiPartyError1146.Adaptive
