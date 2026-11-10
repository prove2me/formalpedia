-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_2
-- name    : LEDPCount.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:15.044197+00:00
-- url     : https://prove2.me/theorems/29421ad1-27f2-47b8-8204-e2aae4cbddac
-- title:
--   Lemma 3.2 — $\mathrm{Var}[\widehat f_H(G)]=O(n^{2k-3}/\varepsilon^{2\ell})$
-- statement:
--   Let $H$ be a pattern with $k$ vertices and $\ell\ge1$ edges. There is a constant $C>0$, depending only on $H$, such that for all $n\ge k$, all $\varepsilon\in(0,1]$ and all graphs $G$ on $[n]$, the estimate of LNC satisfies
--   $$
--   \mathrm{Var}\bigl[\widehat f_H(G)\bigr]\le C\,\frac{n^{2k-3}}{\varepsilon^{2\ell}}.
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - reading: O(n^{2k−3}/ε^{2ℓ}) for a fixed pattern H → ∃ C > 0 depending only on H, uniform in n ≥ k, ε ∈ (0, 1] and G; reason: H is fixed in Theorem 1.1
--   - encoding: Var → evariance in ℝ≥0∞ under the transcript law; reason: Lean convention
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Lemma 3.2, p.19 (PDF p.21), proved to p.21 (PDF p.23)

import Mathlib
import Definitions.Def_LEDPCount_lnc

namespace LEDPCount

open MeasureTheory ProbabilityTheory

/-- Lemma 3.2 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.19, PDF p.21; proved to p.21): `Var[f̂_H(G)] = O(n^{2k−3}/ε^{2ℓ})`.
For every pattern `H` with `k` vertices and `ℓ ≥ 1` edges there is `C > 0` such that for all
`n ≥ k`, `ε ∈ (0, 1]` and graphs `G` on `[n]`, the variance of LNC's estimate is at most
`C n^{2k−3}/ε^{2ℓ}`.

**Formalization Note** `Var` is `evariance` in `ℝ≥0∞` under the transcript law; the
`O(·)` constant depends only on `H`. -/
theorem lemma_3_2 {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ G : SimpleGraph (Fin n),
      evariance (lnc H n ε).output ((lnc H n ε).transcript G) ≤
        ENNReal.ofReal (C * (n : ℝ) ^ (2 * k - 3) / ε ^ (2 * H.edgeFinset.card)) := by sorry

end LEDPCount
