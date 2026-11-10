-- Prove2me | Theorems.Thm_LEDPCount_theorem_1_1
-- name    : LEDPCount.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:41.627309+00:00
-- url     : https://prove2.me/theorems/2a090618-092c-4ca5-ae92-c6418fc7c062
-- title:
--   Theorem 1.1 — LNC is a two-round $\varepsilon$-LEDP algorithm with additive error and RMSE $O(n^{k-3/2}/\varepsilon^{\ell})$
-- statement:
--   Let $H$ be a fixed pattern graph with $k$ vertices and $\ell\ge1$ edges. There is a constant $C>0$, depending only on $H$, such that for every $n\ge k$ and every $\varepsilon\in(0,1]$ the two-round algorithm LNC (Algorithm 1) has the following properties.
--   1. Every randomizer it assigns (each party's round-1 randomized response, and each party's round-2 Laplace release for every round-1 transcript) is an $\varepsilon/2$-local randomizer.
--   2. LNC is $\varepsilon$-LEDP: its transcript law is $\varepsilon$-differentially private for edge-neighboring graphs.
--   3. For every graph $G$ on $[n]$, with $B=C\,n^{k-3/2}/\varepsilon^{\ell}$,
--   $$
--   \mathrm{RMSE}(\widehat f_H;G)=\sqrt{\mathbb E\bigl[(\widehat f_H(G)-f_H(G))^2\bigr]}\le B .
--   $$
--   4. For every graph $G$ on $[n]$,
--   $$
--   \Pr\bigl[|\widehat f_H(G)-f_H(G)|\le B\bigr]\ge\frac23 .
--   $$
--
--   For triangles ($k=\ell=3$) the error is $O(n^{3/2}/\varepsilon^3)$, a factor $\sqrt n$ below the $\Omega(n^2)$ lower bound for noninteractive $\varepsilon$-LEDP triangle counting at fixed small $\varepsilon$.
--
--   **Formalization Note** The pattern is a simple graph on $\mathrm{Fin}\,k$ and the input graph a simple graph on $\mathrm{Fin}\,n$. The RMSE bound is stated for the second moment, $\mathbb E[(\widehat f_H(G)-f_H(G))^2]\le B^2$, in $\mathbb R_{\ge0}\cup\{\infty\}$.
--
--   Differences from the source:
--   - reading: O(n^{k−3/2}/ε^ℓ) for a fixed pattern H → ∃ C > 0 depending only on H, uniform in n ≥ k, ε ∈ (0, 1] and G, one C for the RMSE and the probability bound; reason: H is fixed; the O(·) is in n and ε
--   - reading: a two-round ε-LEDP algorithm → every randomizer is an ε/2-local randomizer, and the transcript law is ε-DP for edge neighbours; reason: Definitions 2.12–2.14: a local algorithm acts only through local randomizers
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: the interactive local model → the two-round fixed-schedule protocol type TwoRoundLocal; reason: LNC has exactly this shape
--   - encoding: RMSE ≤ B → second moment ≤ B² as a lintegral in ℝ≥0∞; reason: B ≥ 0, so the two are equivalent
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_LEDPCount_IsLocalRandomizer
import Definitions.Def_LEDPCount_lnc
import Definitions.Def_LEDPCount_subgraphCount

namespace LEDPCount

open MeasureTheory

/-- Theorem 1.1 (Chen–Peng, *The Power of Interaction in Locally Edge-Private Subgraph Counting*,
arXiv:2611.05038, held version sha256 d18032b0…, p.2, PDF p.4): for any fixed pattern graph `H` with `k` vertices and `ℓ ≥ 1` edges, and
any `ε ∈ (0, 1]`, the two-round algorithm LNC (Algorithm 1) is ε-LEDP and estimates the number of
copies `f_H(G)` with additive error `O(n^{k−3/2}/ε^ℓ)` with probability at least `2/3`; its RMSE
satisfies the same bound.

Precisely: there is `C > 0` depending only on `H` such that for all `n ≥ k` and `ε ∈ (0, 1]`:
(i) each party's randomizer in each round of LNC is an `ε/2`-local randomizer;
(ii) LNC is ε-LEDP (its transcript law is ε-DP for edge-neighbouring graphs);
and for every graph `G` on `[n]`, with `B = C n^{k−3/2}/ε^ℓ`:
(iii) `E[(f̂_H(G) − f_H(G))²] ≤ B²`, i.e. `RMSE(f̂_H; G) ≤ B`;
(iv) `Pr[|f̂_H(G) − f_H(G)| ≤ B] ≥ 2/3`.

**Formalization Note** The pattern is `H : SimpleGraph (Fin k)` and the input graph
`G : SimpleGraph (Fin n)`; LNC is the two-round local algorithm `lnc H n ε`, and the
probability is over its transcript law. The `O(·)` is read as a constant depending only on `H`,
uniform in `n`, `ε` and `G`. `n ≥ k` makes Algorithm 1's `(n − k)!` defined. -/
theorem theorem_1_1 (k : ℕ) (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, k ≤ n → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ i : Fin n, IsLocalRandomizer ((lnc H n ε).round1 i) (ε / 2) ∧
        ∀ y : Fin n → Fin n → Bool, IsLocalRandomizer ((lnc H n ε).round2 i y) (ε / 2)) ∧
      (lnc H n ε).IsLEDP ε ∧
      ∀ G : SimpleGraph (Fin n),
        ∫⁻ t, ENNReal.ofReal (((lnc H n ε).output t - subgraphCount H G) ^ 2)
            ∂((lnc H n ε).transcript G) ≤
          ENNReal.ofReal ((C * (n : ℝ) ^ ((k : ℝ) - 3 / 2) / ε ^ H.edgeFinset.card) ^ 2) ∧
        ENNReal.ofReal (2 / 3) ≤
          (lnc H n ε).transcript G {t | |(lnc H n ε).output t - subgraphCount H G| ≤
            C * (n : ℝ) ^ ((k : ℝ) - 3 / 2) / ε ^ H.edgeFinset.card} := by sorry

end LEDPCount
