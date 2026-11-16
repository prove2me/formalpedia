-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_6_6
-- name    : MatroidSensOracle.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:14:01.120196+00:00
-- url     : https://prove2.me/theorems/1293d05b-8aab-4c59-a995-16b8f58bbf1c
-- title:
--   Theorem 6.6 ($k$ edge-disjoint spanning trees): decision and min-total-cost oracles
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$ and let $k\ge1$. A spanning tree is an acyclic set of $n-1$ edges. Queries are sets $U$ of at most $f$ edge insertions and deletions.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Decision:** preprocessing $C(kn)^{\omega+\tau}$, space $C\,k^2n^2$ words, query $C(f^{\omega+\tau}+f^2k^2)$; output whether $G+U$ has $k$ edge-disjoint spanning trees.
--   2. **Weighted:** preprocessing $\tilde O(W(kn)^3)$, space $C\,W(kn)^3\log_2 n$ bits, query $\tilde O\bigl(Wkn\,(f^{\omega}+f^2k^2)\bigr)$; output the minimum total cost of $k$ edge-disjoint spanning trees (or that none exist).
--
--   By Nash-Williams and Tutte, $k$ edge-disjoint spanning trees certify $k$-edge-connectivity, so these oracles are fault-tolerant connectivity certificates.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1, W ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 6.6, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 6.6 (`k` edge-disjoint spanning trees).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), p.34 (PDF p.37): "Let G = (V, E, c) be an n-vertex undirected graph
with integer edge costs in [−W, W], and let k ⩾ 1. There exist the following sensitivity oracles that,
for any U ∈ E^f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O((kn)^ω) | O(k²n²) | O(f^ω + f²k²) | Whether G + U has k edge-disjoint spanning trees |
| Weighted | Õ(W(kn)³) | O(W(kn)³ log n) | Õ(Wkn · (f^ω + f²k²)) | Min total cost of such k-spanning trees |

§6.2, p.33: "A spanning tree is a maximal acyclic subgraph of G, containing exactly n − 1 edges."

**Formalization Note.**
* Machine, oracle semantics, `ω = omega ℂ`, `O(x^ω)`, `Õ`, space units and "with high
  probability" as in `theorem_6_3`. `P` reads `encodeWith G [n, k, f, W]`, `Q` reads `U.encode`.
* Undirected graphs: every input edge is written `(a, b)` with `a < b` (`InputGraph.Undirected`,
  p.39); an inserted edge joins two distinct vertices and may be parallel to an existing edge; `G + U`
  is the multigraph read undirected. A spanning tree is a forest of `n − 1` edges (`IsSpanningTree`).
* Instances: `n ≥ 2`, `k ≥ 1`, `f ≥ 1`, `W ≥ 1`, costs in `[−W, W]`; queries: any update set of at
  most `f` insertions and deletions with inserted costs in `[−W, W]`.
* Outputs: word `0` is `1` iff `G + U` has `k` pairwise edge-disjoint spanning trees; the weighted
  oracle, when they exist, returns in word `1` (signed) their least total cost. -/
theorem theorem_6_6 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n), 2 ≤ n → 1 ≤ k → 1 ≤ f → 1 ≤ W → G.Undirected →
        G.CostsBounded W → ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), k, f, W]
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let Qs : Set (Update n) := {U | G.ValidU f W U}
          let base : ℝ := (f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2
          let feas : Update n → Prop := fun U => HasKDisjoint (G.plus U) (IsSpanningTree (G.plus U)) k
          let minC : Update n → WithTop ℤ :=
            fun U => minKDisjointCost (G.plus U) (IsSpanningTree (G.plus U)) k
          -- Decision
          O₁.Serves w inp ⌊C * kn ^ (ω + τ)⌋₊ (C * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * w) Qs Update.encode
            ⌊C * base⌋₊ (fun U mQ => Answers (feas U) (minC U) false mQ) err ∧
          -- Weighted
          O₂.Serves w inp ⌊C * W * kn ^ 3 * Real.logb 2 ((W + k + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (C * W * kn ^ 3 * Real.logb 2 n) Qs Update.encode
            ⌊C * W * kn * base * Real.logb 2 ((W + k + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (feas U) (minC U) true mQ) err := by sorry

end MatroidSensOracle.Supplement
