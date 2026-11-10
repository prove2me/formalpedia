-- Prove2me | Theorems.Thm_MultiPartyError1146_Adaptive_decoding_error_tail
-- name    : MultiPartyError1146.Adaptive.decoding_error_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T18:36:07.83024+00:00
-- url     : https://prove2.me/theorems/e59f90af-671e-43ee-b355-266c96eaabc9
-- title:
--   Claim 4.9 — large decoding-error tail
-- statement:
--   For an integer $1\le\phi\le N_r$, both inequalities hold:
--   $$\sum_{k'\ne k}G_{k'}(\cdot,\cdot,\ge\phi)\le L_r\sum_{i\le N_r}\mathbf1_{|E_i|\ge\phi}\le\frac{L_r}{\phi}\sum_{i\le N_r}|E_i|.$$
--   The positive threshold makes division defined and preserves the full two-part tail estimate. The statement also covers arbitrary received-symbol matrices at every positive size; no global corruption-budget premise is needed.
--
--   Differences from the source:
--   - encoding: real-valued pseudocode lengths → ceiling-rounded widths, speaker prefixes and lengths; reason: finite schedules implement the asymptotic pseudocode; exact numerical correctness thresholds are retained
--   - encoding: fixed codes and selectors in Section 4 → actual AlgorithmData satisfying Good, with all local quantities computed by replay; reason: Good contains code/selector quality and uniform length bounds only; no algorithmic invariant or correctness is assumed
--   - generalization: sufficiently large n and the fixed small-budget execution in the surrounding induction setting → every positive n and every input and received-symbol matrix, without a global corruption-budget or induction premise, retaining k outside S1; reason: both inequalities are finite counting bounds for the actual selected sets and error counts, independent of any global budget or asymptotic estimate; the source execution is included
--   - encoding: positive integer threshold φ → 1≤φ with real division; reason: the source integer-index domain excludes zero
--   - encoding: one-based party, time and message-coordinate labels → Fin indices, Boolean bits and optional-Boolean received symbols with zero-based iteration indices; reason: fixed finite relabelings preserve every input, action and error; supporting local quantities are execution-derived
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Claim 4.9, printed p.27, PDF p.29

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Counts

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

theorem decoding_error_tail (n R : ℕ) (hn : 1 ≤ n) (hR : 1 ≤ R) (a : ℝ)
    (D : AlgorithmData n R) (hD : D.Good a) (x : Input n 1)
    (A : Adversary n (duration D)) (r : Fin R) (k : Fin n)
    (hk_good : k ∉ exceptionalInputs D x A)
    (φ : ℕ) (hφ : 1 ≤ φ ∧ φ ≤ prefixSize n R r.val) :
    (∑ k' : Fin n, if k' = k then 0 else
      (Gcount D x A r k k' (fun _ => True) (fun _ => True) (φ ≤ ·) : ℝ)) ≤
      width n R r.val *
        ((Finset.univ.filter fun i => i.val < prefixSize n R r.val ∧
          φ ≤ (decodingErrors D x A r i).card).card : ℝ) ∧
    (width n R r.val : ℝ) *
        ((Finset.univ.filter fun i => i.val < prefixSize n R r.val ∧
          φ ≤ (decodingErrors D x A r i).card).card : ℝ) ≤
      (width n R r.val : ℝ) / φ * totalDecodingErrors D x A r := by sorry

end MultiPartyError1146.Adaptive
