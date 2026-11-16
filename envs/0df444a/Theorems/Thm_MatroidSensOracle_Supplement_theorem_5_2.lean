-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_5_2
-- name    : MatroidSensOracle.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:10:38.680654+00:00
-- url     : https://prove2.me/theorems/f287fcb1-096a-445b-851e-e8dbe392d6a6
-- title:
--   Theorem 5.2 (all-pairs $k$-bounded flow, nearest min-cut and min-cost flow oracles), at the printed query bounds
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex directed graph with unit capacities and integer edge costs in $[-W,W]$, and let $1\le k\le n$. For a query $(s,t,U)$ with $s\ne t$ and $U$ a set of at most $f$ edge insertions and deletions, let
--   $$\lambda^*=\min\bigl(k,\lambda_{G+U}(s,t)\bigr).$$
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and three oracles on the randomized word RAM ($\omega$ the exponent of matrix multiplication) answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Bounded flow:** preprocessing $C(kn)^{\omega+\tau}$, space $C\,k^2n^2$ words, query $C\,(f^{\omega+\tau}+f^2k^2)\log_2(k+1)$; output $\lambda^*$.
--   2. **Nearest min-cut:** preprocessing $C(kn)^{\omega+\tau}$, space $C\,k^2n^2$ words, query $C\,(f^{\omega+\tau}+f^2k^2)\,n\log_2(k+1)$; output the source side of $\mathrm{NMC}_{G+U}(s,t)$ whenever $\lambda^*<k$.
--   3. **Min-cost flow:** preprocessing $\tilde O(W(kn)^3)$, space $C\,W(kn)^3$ words, query $\tilde O\bigl((f^{\omega}+f^2k^2)\,kWn\bigr)$; output the least cost of an $(s,t)$-flow of value $\lambda^*$ in $G+U$.
--
--   This is the all-pairs bounded-flow oracle on which the fixed-pair oracles of Theorem 5.5 are built.
--
--   **Formalization Note** The query bounds are stated as printed. The paper's proof bounds each test by $O((k+f)^4)$, which exceeds the printed $O(f^\omega+f^2k^2)$ when $k$ is large; the statement is not weakened to the proof's bound.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: log k → log₂(k + 1); reason: so that k = 1 does not zero the bound
--   - encoding: (s, t) ∈ V² → s ≠ t; reason: (s, t)-cuts and NMC_{G+U}(s, t) are defined only for s ≠ t (p.12)
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, 1 ≤ k ≤ n, f ≥ 1, W ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
--   - encoding: outputs λ∗, NMC_{G+U}(s, t), a cost → word 0 of the query memory; the low bits of words 0, …, n − 1 for the source side; word 0 signed; reason: base output convention
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 5.2, pp.26–27 (PDF pp.29–30)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 5.2 (all-pairs `k`-bounded flow oracles).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), pp.26–27 (PDF pp.29–30): "Let G = (V, E, c) be an n-vertex directed
graph with integer costs in [−W, W], and k ∈ [1, n]. Then there exist the following sensitivity
oracles that, for any query (s, t, U) ∈ V² × E^f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Bounded Flow | O((kn)^ω) | O(k²n²) | O((f^ω + f²k²) log k) | λ∗ = min(k, λ_{G+U}(s, t)) |
| Nearest Min-Cut | O((kn)^ω) | O(k²n²) | O((f^ω + f²k²) · n log k) | NMC_{G+U}(s, t) (if λ∗ < k) |
| Min-Cost Flow | Õ(W(kn)³) | O(W(kn)³) | Õ((f^ω + f²k²) · kWn) | Min-cost for flow of value λ∗ |

**Formalization Note.**
* Machine and oracle semantics: the base randomized word RAM (`Oracle.run`); `P` reads
  `encodeWith G [n, k, f, W]`, `Q` reads only the stored string and the query words
  `[s, t] ++ U.encode`; programs work for every word width `w ≥ b(⌊log₂(n + k + f + W + 2)⌋ + 1)`.
* `ω = omega ℂ`; `O(x^ω)` is `C x^{ω+τ}` for every `τ > 0`; `log k` is `log₂(k + 1)`; `Õ(X)` is
  `C X (log₂(Z + 2))^K` with `Z` the sum of the parameters in `X`.
* Space: the printed bounds `O(k²n²)`, `O(W(kn)³)` contain no `log n` and count machine words, i.e.
  `C X w` bits.
* With high probability: for every `c > 0` each fixed query errs with probability at most `n^{−c}`.
* Instances: `n ≥ 2`, `1 ≤ k ≤ n`, `f ≥ 1`, `W ≥ 1`, costs in `[−W, W]`; queries: `s ≠ t` and any
  update set `U` of at most `f` insertions and deletions (`F ⊆ E`, inserted costs in `[−W, W]`);
  `G + U` is a multigraph.
* Outputs: word `0` is `λ∗`; the low bits of words `0, …, n − 1` mark the source side of
  `NMC_{G+U}(s, t)` (required only when `λ∗ < k`); word `0` (signed) is the least cost of an
  `(s, t)`-flow of value `λ∗` in `G + U`. -/
theorem theorem_5_2 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n), 2 ≤ n → 1 ≤ k → k ≤ n → 1 ≤ f → 1 ≤ W →
        G.CostsBounded W → ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), k, f, W]
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let Qs : Set (Fin n × Fin n × Update n) := {q | q.1 ≠ q.2.1 ∧ G.ValidUpdate f W q.2.2}
          let enc : Fin n × Fin n × Update n → List ℤ :=
            fun q => [((q.1 : ℕ) : ℤ), ((q.2.1 : ℕ) : ℤ)] ++ q.2.2.encode
          let lam : Fin n × Fin n × Update n → ℕ :=
            fun q => min k ((G.plus q.2.2).maxFlow q.1 q.2.1)
          let base : ℝ := (f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2
          let lgk : ℝ := Real.logb 2 ((k : ℝ) + 1)
          let TP₁ : ℕ := ⌊C * kn ^ (ω + τ)⌋₊
          let TP₃ : ℕ := ⌊C * W * kn ^ 3 * Real.logb 2 ((W + k + n : ℕ) + 2 : ℝ) ^ K⌋₊
          -- Bounded Flow
          O₁.Serves w inp TP₁ (C * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * w) Qs enc ⌊C * base * lgk⌋₊
            (fun q mQ => (mQ 0).toNat = lam q) err ∧
          -- Nearest Min-Cut (if λ∗ < k)
          O₂.Serves w inp TP₁ (C * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * w) Qs enc ⌊C * base * n * lgk⌋₊
            (fun q mQ => lam q < k → (G.plus q.2.2).IsNearestMinCut q.1 q.2.1 (outSet mQ)) err ∧
          -- Min-Cost Flow of value λ∗
          O₃.Serves w inp TP₃ (C * W * kn ^ 3 * w) Qs enc
            ⌊C * base * k * W * n * Real.logb 2 ((f + k + W + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun q mQ => ((mQ 0).toInt : WithTop ℤ) =
              (G.plus q.2.2).minCostFlow q.1 q.2.1 (lam q)) err := by sorry

end MatroidSensOracle.Supplement
