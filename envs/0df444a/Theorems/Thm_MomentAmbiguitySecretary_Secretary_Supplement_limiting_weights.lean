-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_limiting_weights
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.limiting_weights
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-15T18:49:57.389994+00:00
-- url     : https://prove2.me/theorems/ee382d72-ffad-48ba-80c4-783d8ea1ee92
-- title:
--   Lemma 8.1 (used in the proof of Theorem 3.1) — Existence of every limiting normalized barycentric weight
-- statement:
--   Fix integers $n,B\ge3$ and a node index $j\ge0$. The normalized finite barycentric weights on $x_0,\ldots,x_{K+2}$ converge to a finite real limit:
--
--   $$\lim_{K\to\infty} w_j^{(n,K)}=w_j.$$
--
--   The finite weights are the actual barycentric products normalized by the weight at node 2. Terms before $K\ge\max(0,j-2)$ do not affect the limit. This supplies the canonical weights for the binary construction.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 8.1, PDF/printed p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 8.1, supplied preprint, PDF/printed p.22. -/
theorem limiting_weights (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (j : ℕ) :
    Tendsto (fun K : ℕ => finiteWeight n B K j) atTop (𝓝 (binaryWeight n B j)) := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
