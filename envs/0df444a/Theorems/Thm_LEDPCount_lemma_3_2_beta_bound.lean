-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_2_beta_bound
-- name    : LEDPCount.lemma_3_2_beta_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:07.155224+00:00
-- url     : https://prove2.me/theorems/da120958-973f-43c4-ac07-32047c53ff02
-- title:
--   Proof of Lemma 3.2 — $\mathrm{Var}[\beta]\le(\ell-1)^2\max(V,1)^\ell|\mathrm{Aut}(H)|^{-2}\sum_{c=3}^k g_H(n,c)$
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, $n\ge k$, $\varepsilon\in(0,1]$, $\varepsilon_0=\varepsilon/2$ and $V=e^{\varepsilon_0}/(e^{\varepsilon_0}-1)^2$. For every graph $G$ on $[n]$, with $\beta=P(X)+\sum_iQ_i-f_H(G)$ under the transcript law of LNC,
--   $$
--   \mathrm{Var}[\beta]\le\frac{(\ell-1)^2\cdot\max(V,1)^{\ell}}{|\mathrm{Aut}(H)|^2}\sum_{c=3}^{k}g_H(n,c).
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: Var[β] → evariance in ℝ≥0∞ under the transcript law; reason: Lean convention
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Lemma 3.2, reduction to g_H, p.20 (PDF p.22)

import Mathlib
import Definitions.Def_LEDPCount_lnc
import Definitions.Def_LEDPCount_subgraphCount
import Definitions.Def_LEDPCount_gH

namespace LEDPCount

open MeasureTheory ProbabilityTheory

/-- Proof of Lemma 3.2, reduction to `g_H` (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.20, PDF p.22): with
`β := P(X) + ∑_i Q_i − f_H(G)` and `V = e^{ε₀}/(e^{ε₀} − 1)²`, `ε₀ = ε/2`,
`Var[β] ≤ (ℓ − 1)² max(V, 1)^ℓ / |Aut(H)|² · ∑_{c=3}^{k} g_H(n, c)`, for a pattern with `ℓ ≥ 1`
edges, `n ≥ k`, `ε ∈ (0, 1]` and every graph `G`.

**Formalization Note** `Var` is `evariance` in `ℝ≥0∞` under the transcript law. -/
theorem lemma_3_2_beta_bound {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : SimpleGraph (Fin n)) :
    evariance (fun t : (Fin n → Fin n → Bool) × (Fin n → ℝ) =>
        countPoly H (lncX ε t.1) + ∑ i, lncQ H ε i (adjRow G i) t.1 - subgraphCount H G)
      ((lnc H n ε).transcript G) ≤
    ENNReal.ofReal (((H.edgeFinset.card : ℝ) - 1) ^ 2 *
        max (Real.exp (ε / 2) / (Real.exp (ε / 2) - 1) ^ 2) 1 ^ H.edgeFinset.card /
        (autCount H : ℝ) ^ 2 * ∑ c ∈ Finset.Icc 3 k, (gH H n c : ℝ)) := by sorry

end LEDPCount
