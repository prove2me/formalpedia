-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_limiting_decay
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.limiting_decay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:50:36.460989+00:00
-- url     : https://prove2.me/theorems/f59134ce-4a36-4fe3-9c59-51e6a499515d
-- title:
--   Lemma 8.2 (used in the proof of Theorem 3.1) — Explicit all-orders decay for every limiting weight
-- statement:
--   Fix integers $n,B\ge3$. For every integer $M\ge1$, let
--   $$L_M=\max\left(0,\left\lceil\frac{M-2}{1-1/B}\right\rceil\right),\qquad
--    C_M^{(0,1,2)}=\max\{2n,2nB^M,(nB)^M\},$$
--   $$C_M^{(\ge3)}=\begin{cases}8(nB)^2&M=1,2,\\8(nB)^2\max\{x_{L_M+2}^{M-2},2^{L_M}\}&M\ge3,\end{cases}\qquad C_M=\max\{C_M^{(0,1,2)},C_M^{(\ge3)}\}.$$
--   Then the canonical limiting weights satisfy
--   $$|w_j|\le C_M/x_j^M\quad(j\ge0).$$
--   This is an all-orders bound with the displayed constants, including the first three nodes.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 8.2, PDF/printed p.23-24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Binary

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 8.2, supplied preprint, PDF/printed p.23-24. -/
theorem limiting_decay (n B : ℕ) (hn : 3 ≤ n) (hB : 3 ≤ B) (M : ℕ) (hM : 1 ≤ M) :
    ∀ j : ℕ, |binaryWeight n B j| ≤ decayC n B M / (binaryNode n B j : ℝ) ^ M := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
