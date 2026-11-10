-- Prove2me | Theorems.Thm_LEDPCount_lemma_3_2_alpha
-- name    : LEDPCount.lemma_3_2_alpha
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:50.716585+00:00
-- url     : https://prove2.me/theorems/40e07be7-a509-4c93-b8a5-f78f99ba8344
-- title:
--   Proof of Lemma 3.2 — $\mathrm{Var}[\alpha]=2nb^2=O(n^{2k-3}/\varepsilon^{2\ell})$
-- statement:
--   1. For every $n$ and $b>0$, the sum $\alpha=\sum_{i=1}^n Y_i$ of $n$ independent $\mathrm{Lap}(b)$ variables has $\mathrm{Var}[\alpha]=2nb^2$.
--   2. Let $H$ have $k$ vertices and $\ell\ge1$ edges and let $b=2\ell(n-2)!\kappa^{\ell-1}/(|\mathrm{Aut}(H)|(n-k)!\varepsilon_0)$ be the Laplace scale of LNC. There is $C>0$, depending only on $H$, such that for all $n\ge k$ and $\varepsilon\in(0,1]$,
--   $$
--   2nb^2\le C\,\frac{n^{2k-3}}{\varepsilon^{2\ell}}.
--   $$
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - reading: O(n^{2k−3}/ε^{2ℓ}) for a fixed pattern H → ∃ C > 0 depending only on H, uniform in n ≥ k and ε ∈ (0, 1]; reason: H is fixed in Theorem 1.1
--   - encoding: Var[α] → evariance in ℝ≥0∞; reason: Lean convention
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Lemma 3.2, Laplace term, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_LEDPCount_lnc

namespace LEDPCount

open MeasureTheory ProbabilityTheory

/-- Proof of Lemma 3.2, the Laplace term (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.21, PDF p.23):
1. the sum `α` of `n` independent `Lap(b)` variables, `b > 0`, has `Var[α] = 2nb²`;
2. for LNC's scale `b = 2ℓ(n−2)!κ^{ℓ−1}/(|Aut(H)|(n−k)!ε₀)`, `2nb² = O(n^{2k−3}/ε^{2ℓ})`, with a
   constant depending only on `H`, uniformly in `n ≥ k` and `ε ∈ (0, 1]`.

**Formalization Note** `Var` is `evariance` in `ℝ≥0∞`. -/
theorem lemma_3_2_alpha {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) :
    (∀ (n : ℕ) (b : ℝ), 0 < b →
      evariance (fun z : Fin n → ℝ => ∑ i, z i)
          (Measure.pi fun _ : Fin n => PrivLearn.Generic.laplace b) =
        ENNReal.ofReal (2 * n * b ^ 2)) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      2 * (n : ℝ) * lncScale H n ε ^ 2 ≤
        C * (n : ℝ) ^ (2 * k - 3) / ε ^ (2 * H.edgeFinset.card) := by sorry

end LEDPCount
