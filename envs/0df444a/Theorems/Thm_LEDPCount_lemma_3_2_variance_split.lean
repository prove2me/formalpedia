-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_2_variance_split
-- name    : LEDPCount.lemma_3_2_variance_split
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:56.087031+00:00
-- url     : https://prove2.me/theorems/48b962d8-b8b8-45f7-9d93-b9484f944ede
-- title:
--   Proof of Lemma 3.2 — $\mathrm{Var}[\widehat f_H(G)]=\mathrm{Var}[\beta]+\mathrm{Var}[\alpha]$
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, $n\ge k$, $\varepsilon\in(0,1]$ and $G$ a graph on $[n]$. On a transcript $(y,m)$ of LNC put
--   $$
--   \beta=P(X)+\sum_{i=1}^n Q_i-f_H(G),\qquad \alpha=\sum_{i=1}^n (M_i-Q_i),
--   $$
--   so that $\alpha$ is the sum of the $n$ Laplace noises. Then
--   $$
--   \mathrm{Var}\bigl[\widehat f_H(G)\bigr]=\mathrm{Var}[\beta]+\mathrm{Var}[\alpha].
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: α = ∑ᵢ Lap(…) → α = ∑ᵢ (Mᵢ − Qᵢ) on the transcript; reason: Mᵢ = Qᵢ + Lap(…)
--   - encoding: Var → evariance in ℝ≥0∞ under the transcript law; reason: Lean convention
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Lemma 3.2, variance split, p.19 (PDF p.21)

import Mathlib
import Definitions.Def_LEDPCount_lnc
import Definitions.Def_LEDPCount_subgraphCount

namespace LEDPCount

open MeasureTheory ProbabilityTheory

/-- Proof of Lemma 3.2, variance split (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.19, PDF p.21): with
`β := P(X) + ∑_i Q_i − f_H(G)` and `α := ∑_i (M_i − Q_i)` (the sum of the `n` Laplace noises),
`Var[f̂_H(G)] = Var[β] + Var[α]`, for a pattern with `ℓ ≥ 1` edges, `n ≥ k`, `ε ∈ (0, 1]` and
every graph `G`.

**Formalization Note** Variances are `evariance` in `ℝ≥0∞` under the transcript law `(y, m)`;
`Q_i` is computed from `y` and party `i`'s row. -/
theorem lemma_3_2_variance_split {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (G : SimpleGraph (Fin n)) :
    evariance (lnc H n ε).output ((lnc H n ε).transcript G) =
      evariance (fun t : (Fin n → Fin n → Bool) × (Fin n → ℝ) =>
          countPoly H (lncX ε t.1) + ∑ i, lncQ H ε i (adjRow G i) t.1 - subgraphCount H G)
        ((lnc H n ε).transcript G) +
      evariance (fun t : (Fin n → Fin n → Bool) × (Fin n → ℝ) =>
          ∑ i, (t.2 i - lncQ H ε i (adjRow G i) t.1))
        ((lnc H n ε).transcript G) := by sorry

end LEDPCount
