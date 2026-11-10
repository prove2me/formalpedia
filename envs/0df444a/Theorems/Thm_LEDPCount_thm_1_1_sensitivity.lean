-- Prove2me | Theorems.Thm_LEDPCount_thm_1_1_sensitivity
-- name    : LEDPCount.thm_1_1_sensitivity
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:59.724724+00:00
-- url     : https://prove2.me/theorems/eaffaa95-08d9-4499-807c-e570367ba62c
-- title:
--   Proof of Theorem 1.1 — $\kappa=O(1/\varepsilon)$ and the sensitivity bound $\Delta_Q\le 2\ell(n-2)!\kappa^{\ell-1}/(|\mathrm{Aut}(H)|(n-k)!)$
-- statement:
--   Let $H$ have $k$ vertices and $\ell\ge1$ edges, let $n\ge k$, $\varepsilon_0=\varepsilon/2$ and $\kappa=e^{\varepsilon_0}/(e^{\varepsilon_0}-1)$.
--   1. $\kappa=O(1/\varepsilon)$: there is $c>0$ with $\kappa\le c/\varepsilon$ for all $\varepsilon\in(0,1]$.
--
--   For every $\varepsilon\in(0,1]$:
--
--   2. every debiased bit $X_{i,j}$ satisfies $|X_{i,j}|\le\kappa$ and $|X_{i,j}-A_{i,j}|\le\kappa$ for $A_{i,j}\in\{0,1\}$;
--   3. for every symmetric $X$ with all entries of absolute value at most $\kappa$ and all $i\ne j$,
--   $$
--   \left|\frac{\partial P(X)}{\partial X_{i,j}}\right|\le\frac{2\ell\,(n-2)!\,\kappa^{\ell-1}}{|\mathrm{Aut}(H)|\,(n-k)!};
--   $$
--   4. for every round-1 transcript and all graphs $G,G'$ whose edge sets differ exactly in $\{i,j\}$ with $i<j$, $\|Q(G)-Q(G')\|_1=|\partial P(X)/\partial X_{i,j}|$, where $Q=(Q_1,\dots,Q_n)$ are the round-2 statistics of LNC;
--   5. consequently $\Delta_Q=\max_{G\sim G'}\|Q(G)-Q(G')\|_1$ obeys the bound of item 3.
--
--   This is the sensitivity that calibrates the Laplace noise of the second round.
--
--   Differences from the source:
--   - encoding: Algorithm 1 for a pattern on k vertices and an n-vertex graph → n ≥ k assumed; reason: line 11's (n − k)! is undefined for n < k; Theorem 1.1's setting
--   - encoding: (n − 2)!/(n − k)! → Nat.descFactorial (n − 2) (k − 2); reason: equal for 2 ≤ k ≤ n
--   - encoding: Δ_Q = max_{G∼G′} ∥Q(G) − Q(G′)∥₁ = max_{i<j} |∂P/∂X_{i,j}| → for each neighbouring pair differing in {i, j}, ∥Q(G) − Q(G′)∥₁ = |∂P/∂X_{i,j}|, and every neighbouring pair obeys the bound; reason: the maximum stated pointwise
--   - encoding: κ = O(1/ε) → ∃ c > 0 with κ ≤ c/ε for all ε ∈ (0, 1]; reason: the meaning of O(1/ε) on Theorem 1.1's range
--   - generalization: |∂P(X)/∂X_{i,j}| bounded for X a fixed first-round transcript of LNC → bounded for every symmetric real X with all |X_e| ≤ κ, and the ∥Q(G) − Q(G′)∥₁ clauses for every round-1 message vector y in Fin n → Fin n → Bool (including the padding coordinates); reason: the proof uses only |X_e| ≤ κ; every LNC transcript satisfies it (clause 2), so this specializes to the source
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), proof of Theorem 1.1, sensitivity bound, p.18–19 (PDF p.20–21)

import Mathlib
import Definitions.Def_LEDPCount_lnc

namespace LEDPCount

/-- Proof of Theorem 1.1, sensitivity bound (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.18–19, PDF p.20–21). Let `H`
have `k` vertices and `ℓ ≥ 1` edges, `n ≥ k`, `ε₀ = ε/2` and `κ = e^{ε₀}/(e^{ε₀} − 1)`.
1. `κ = O(1/ε)` on `ε ∈ (0, 1]`.
2. For `ε ∈ (0, 1]`: every debiased bit satisfies `|X_{i,j}| ≤ κ` and `|X_{i,j} − A_{i,j}| ≤ κ`;
   for every `X` with all `|X_e| ≤ κ` and `i ≠ j`,
   `|∂P(X)/∂X_{i,j}| ≤ 2ℓ(n−2)!κ^{ℓ−1}/(|Aut(H)|(n−k)!)`; for every round-1 transcript and
   graphs `G, G'` whose edge sets differ exactly in `{i, j}`, `i < j`,
   `‖Q(G) − Q(G')‖₁ = |∂P(X)/∂X_{i,j}|`; hence `Δ_Q = max_{G∼G'} ‖Q(G) − Q(G')‖₁` obeys the
   same bound.

**Formalization Note** `(n − 2)!/(n − k)!` is `Nat.descFactorial (n − 2) (k − 2)`. -/
theorem thm_1_1_sensitivity {k : ℕ} (H : SimpleGraph (Fin k)) [DecidableRel H.Adj]
    (hℓ : 1 ≤ H.edgeFinset.card) (n : ℕ) (hkn : k ≤ n) :
    (∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → kappa ε ≤ c / ε) ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∀ y a : Bool, |debias (ε / 2) y| ≤ kappa ε ∧
        |debias (ε / 2) y - (if a then 1 else 0)| ≤ kappa ε) ∧
      (∀ X : Sym2 (Fin n) → ℝ, (∀ e, |X e| ≤ kappa ε) → ∀ i j : Fin n, i ≠ j →
        |partialP H X s(i, j)| ≤
          2 * (H.edgeFinset.card : ℝ) * (Nat.descFactorial (n - 2) (k - 2) : ℝ) *
            kappa ε ^ (H.edgeFinset.card - 1) / (autCount H : ℝ)) ∧
      (∀ y : Fin n → Fin n → Bool, ∀ G G' : SimpleGraph (Fin n), ∀ i j : Fin n, i < j →
        symmDiff G.edgeSet G'.edgeSet = {s(i, j)} →
        ∑ m, |lncQ H ε m (adjRow G m) y - lncQ H ε m (adjRow G' m) y| =
          |partialP H (lncX ε y) s(i, j)|) ∧
      (∀ y : Fin n → Fin n → Bool, ∀ G G' : SimpleGraph (Fin n), EdgeNeighbors G G' →
        ∑ i, |lncQ H ε i (adjRow G i) y - lncQ H ε i (adjRow G' i) y| ≤
          2 * (H.edgeFinset.card : ℝ) * (Nat.descFactorial (n - 2) (k - 2) : ℝ) *
            kappa ε ^ (H.edgeFinset.card - 1) / (autCount H : ℝ)) := by sorry

end LEDPCount
