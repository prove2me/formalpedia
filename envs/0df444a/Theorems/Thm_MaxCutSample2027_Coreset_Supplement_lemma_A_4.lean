-- Prove2me | Theorems.Thm_MaxCutSample2027_Coreset_Supplement_lemma_A_4
-- name    : MaxCutSample2027.Coreset.Supplement.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:09:39.877796+00:00
-- url     : https://prove2.me/theorems/aef37687-aa98-4fde-ad22-db3214df1cdf
-- title:
--   Lemma A.4 — absolute-value Massart inequality
-- statement:
--   Let $m,r\ge1$ be integers, let $a_{ij}\in\mathbb R$ for $1\le i\le m$ and $1\le j\le r$, and let all $mr$ signs $\sigma_{ij}$ be independent and uniform in $\{-1,+1\}$. Then
--   $$\mathbb E_\sigma\max_{1\le j\le r}\left|\sum_{i=1}^m\sigma_{ij}a_{ij}\right|\le\sqrt{2\log(2r)}\max_{1\le j\le r}\sqrt{\sum_{i=1}^ma_{ij}^2}.$$
--   The logarithm is natural. The maximum is over absolute column sums and there is no normalization by $m$. This is the per-column absolute-value form used for the signed-maximum estimate.
--
--   Differences from the source:
--   - encoding: expectations over independent uniform signs → uniform finite sums over Boolean sign vectors or matrices; reason: false denotes +1 and true denotes -1; each sign assignment receives its exact uniform probability
--   - encoding: natural logarithm and finite column maxima → Real.log and real sSup over Fin r; reason: r ≥ 1 makes both column ranges nonempty and finite, and 2r > 0
-- source:
--   Itamar Bender, Robert Krauthgamer, STOC 2027 submission #147 (October 2026), Lemma A.4, p. 35. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/147.pdf (PDF SHA-256 54bb82836bdc80e7729d444c36f7299cb7d50838d4ee557decb3495e61236fa7; printed page = PDF page).

import Definitions.Def_MaxCutSample2027_Coreset_Supplement_sampling
open scoped BigOperators
noncomputable section

namespace MaxCutSample2027.Coreset.Supplement

theorem lemma_A_4 (m r : ℕ) (hm : 1 ≤ m) (hr : 1 ≤ r) (a : Fin m → Fin r → ℝ) :
    matrixSignAverage m r (fun σ => sSup (Set.range (fun j : Fin r =>
      |∑ i, signValue (σ i j) * a i j|))) ≤
    Real.sqrt (2 * Real.log (2 * (r : ℝ))) *
      sSup (Set.range (fun j : Fin r => Real.sqrt (∑ i, a i j ^ 2))) := by sorry

end MaxCutSample2027.Coreset.Supplement
