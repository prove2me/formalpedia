-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_binary_all_moments
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.binary_all_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:52:09.118798+00:00
-- url     : https://prove2.me/theorems/2279e69f-cf0e-41ef-899c-c3e7e865699c
-- title:
--   Lemma 8.5 (used in the proof of Theorem 3.1) — Finiteness and equality of every moment of the binary laws
-- statement:
--   Fix integers $n,B\ge3$. For every natural $s$, the two canonical probability-weight series are finite and equal:
--   $$\sum_{j\ge0}x_j^sp_j=\sum_{j\ge0}x_j^sq_j<\infty.$$
--   Equivalently, the raw atomic measures $\nu$ and $\mu$ have integrable $s$-th powers and identical $s$-th moments. Summability and integrability are asserted explicitly. This includes order zero and establishes full moment agreement.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 8.5, PDF/printed p.27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 8.5, supplied preprint, PDF/printed p.27. -/
theorem binary_all_moments (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    Summable (fun j : ℕ => (binaryNode n B j : ℝ) ^ s * binaryP n B j) ∧
    Summable (fun j : ℕ => (binaryNode n B j : ℝ) ^ s * binaryQ n B j) ∧
    (∑' j : ℕ, (binaryNode n B j : ℝ) ^ s * binaryP n B j) =
      (∑' j : ℕ, (binaryNode n B j : ℝ) ^ s * binaryQ n B j) ∧
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ s) (binaryNu n B) ∧
    Integrable (fun x : ℝ≥0 => (x : ℝ) ^ s) (binaryMu n B) ∧
    (∫ x : ℝ≥0, (x : ℝ) ^ s ∂binaryNu n B) =
      (∫ x : ℝ≥0, (x : ℝ) ^ s ∂binaryMu n B) := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
