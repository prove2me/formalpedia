-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_1
-- name    : LEDPCount.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:04.399819+00:00
-- url     : https://prove2.me/theorems/1dfc7b1f-65db-4df9-a465-a77da7489329
-- title:
--   Lemma 3.1 — LNC is unbiased, $\mathbb E[\widehat f_H(G)]=f_H(G)$
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, $n\ge k$ and $\varepsilon\in(0,1]$. For every graph $G$ on $[n]$ the estimate $\widehat f_H(G)$ of LNC is integrable and
--   $$
--   \mathbb E\bigl[\widehat f_H(G)\bigr]=f_H(G),
--   $$
--   the expectation taken over the transcript law of Algorithm 1.
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: E[f̂_H(G)] → f̂_H(G) integrable and its integral under the transcript law; reason: a Bochner integral of a non-integrable function is 0
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Lemma 3.1, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_LEDPCount_lnc
import Definitions.Def_LEDPCount_subgraphCount

namespace LEDPCount

open MeasureTheory

/-- Lemma 3.1 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.19, PDF p.21): LNC is unbiased, `E[f̂_H(G)] = f_H(G)`, for a
pattern `H` with `k` vertices and `ℓ ≥ 1` edges, `n ≥ k`, `ε ∈ (0, 1]` and every graph `G`
on `[n]`; the expectation is over the transcript law of Algorithm 1.

**Formalization Note** Integrability of the estimate is part of the statement. -/
theorem lemma_3_1 {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : SimpleGraph (Fin n)) :
    Integrable (lnc H n ε).output ((lnc H n ε).transcript G) ∧
    ∫ t, (lnc H n ε).output t ∂((lnc H n ε).transcript G) = subgraphCount H G := by sorry

end LEDPCount
