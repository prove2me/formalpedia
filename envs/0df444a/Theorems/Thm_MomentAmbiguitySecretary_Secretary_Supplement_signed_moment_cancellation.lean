-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_signed_moment_cancellation
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.signed_moment_cancellation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:41.517231+00:00
-- url     : https://prove2.me/theorems/38cb039a-d4e5-47aa-a665-8e54c33adfcc
-- title:
--   Lemma 8.4 (used in the proof of Theorem 3.1) — Every signed moment sum vanishes
-- statement:
--   Fix integers $n,B\ge3$. For every natural moment order $s$, including zero, the signed series converges and
--   $$\sum_{j\ge0}w_jx_j^s=0.$$
--   Convergence is part of the assertion, so the zero is the sum of an actual convergent series. This is the infinite signed cancellation identity behind the binary moment matching.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 8.4, PDF/printed p.26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 8.4, supplied preprint, PDF/printed p.26. -/
theorem signed_moment_cancellation (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (s : ℕ) :
    HasSum (fun j : ℕ => binaryWeight n B j * (binaryNode n B j : ℝ) ^ s) 0 := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
