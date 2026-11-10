-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_low_lead_bound
-- name    : MultiPartyError1146.Adaptive.low_lead_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:35:57.424502+00:00
-- url     : https://prove2.me/theorems/d67a8fed-3202-4148-81af-a5a7032e890e
-- title:
--   Corollary 4.10 — time with low correct cushion
-- statement:
--   For $k\notin S_1$ and an integer $1\le\tau\le N_r$, the number of speakers after whom the correct signed vote is at most $\tau$ obeys both source inequalities:
--   $$N_{\rm low}\le F(\le\tau)+\frac1{L_r}\sum_{k'\ne k}G_{k'}(\le\tau,\cdot,\cdot)\le\frac{4n\tau}{L_r}+2|E'_k|+\frac4\tau\sum_i|E_i|+\frac2{L_r}\sum_{k'\ne k}|E'_{k'}|.$$
--   All sums are finite execution counts. This is the complete low-cushion bound, including its intermediate expression. The statement also covers arbitrary received-symbol matrices at every positive size; no global corruption-budget premise is needed.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths → ceiling-rounded widths, speaker prefixes and lengths; reason: finite schedules implement the asymptotic pseudocode; exact numerical correctness thresholds are retained
--   - encoding: fixed codes and selectors in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - generalization: sufficiently large n and the fixed small-budget execution in the surrounding induction setting → every positive n and every input and received-symbol matrix, without a global corruption-budget or induction premise, retaining k outside S1; reason: the two inequalities use only the preceding combinatorial bounds and 1≤Lr≤n, not the global budget or induction estimates; the source execution is included
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Corollary 4.10, printed p.27, PDF p.29

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem low_lead_bound (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (a : ℝ)
    (D : AlgorithmData n R) (hD : D.Good a) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n)
    (hk_good : k ∉ exceptionalInputs D x A)
    (τ : ℤ)
    (hτ : 1 ≤ τ ∧ τ ≤ prefixSize n R r.val) :
    (lowLeadCount D x A r k τ : ℝ) ≤
      Fcount D x A r k (· ≤ τ) + (1 : ℝ) / width n R r.val *
        (∑ k' : Fin n, if k' = k then 0 else
          (Gcount D x A r k k' (· ≤ τ) (fun _ => True) (fun _ => True) : ℝ)) ∧
    (Fcount D x A r k (· ≤ τ) : ℝ) + (1 : ℝ) / width n R r.val *
        (∑ k' : Fin n, if k' = k then 0 else
          (Gcount D x A r k k' (· ≤ τ) (fun _ => True) (fun _ => True) : ℝ)) ≤
      4 * n * (τ : ℝ) / width n R r.val + 2 * (wrongSpeakers D x A r k).card +
        4 / (τ : ℝ) * totalDecodingErrors D x A r +
        2 / (width n R r.val : ℝ) * otherWrongCount D x A r k := by sorry

end MultiPartyError1146.Adaptive
