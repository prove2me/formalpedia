-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_finite_decay
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.finite_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:51:03.363604+00:00
-- url     : https://prove2.me/theorems/bb534c73-bba4-4b06-bb59-21e38d959ba2
-- title:
--   Lemma 8.3 (used in the proof of Theorem 3.1) — The same explicit decay bound uniformly in the finite truncation
-- statement:
--   Fix integers $n,B\ge3$ and $M\ge1$, with the same explicit $C_M$ as in Lemma 8.2. Every finite normalized barycentric vector obeys
--   $$|w_j^{(n,K)}|\le C_M/x_j^M\qquad(K\ge0,\ 0\le j\le K+2).$$
--   The constant is independent of the truncation $K$. This uniformity permits passage of moment identities to the infinite construction.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 8.3, PDF/printed p.25; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 8.3, supplied preprint, PDF/printed p.25. -/
theorem finite_decay (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (M : ℕ) (hM : 1 ≤ M) :
    ∀ K j : ℕ, j ≤ K + 2 →
      |finiteWeight n B K j| ≤ decayC n B M / (binaryNode n B j : ℝ) ^ M := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
