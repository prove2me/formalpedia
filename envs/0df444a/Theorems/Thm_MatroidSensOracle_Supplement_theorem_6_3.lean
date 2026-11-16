-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_6_3
-- name    : MatroidSensOracle.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:12:57.319814+00:00
-- url     : https://prove2.me/theorems/db01b9cf-cd38-4eb6-83c0-bd65e0935261
-- title:
--   Theorem 6.3 ($k$-disjoint $s$-rooted arborescences): decision and min-total-cost oracles
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex directed graph with integer edge costs in $[-W,W]$ and let $k\ge1$. An **$s$-rooted spanning arborescence** of a directed multigraph is a set of $n-1$ edges forming a spanning tree of the underlying undirected graph in which $s$ has no incoming edge and every other vertex exactly one. A query is a root $s\in V$ and a set $U$ of at most $f$ edge insertions and deletions.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Decision:** preprocessing $C(kn)^{\omega+\tau}$, space $C\,k^2n^2$ words, query $C(f^{\omega+\tau}+f^2k^2)$; output whether $G+U$ has $k$ pairwise edge-disjoint $s$-rooted spanning arborescences.
--   2. **Weighted:** preprocessing $\tilde O(W(kn)^3)$, space $C\,W(kn)^3\log_2 n$ bits, query $\tilde O\bigl(Wkn\,(f^{\omega}+f^2k^2)\bigr)$; output the minimum total cost of such a family (or that none exists).
--
--   By Edmonds' theorem the decision oracle also yields $k$-strong-connectivity oracles (Corollary 6.4).
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1, W ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 6.3, p.33 (PDF p.36)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 6.3 (`k`-disjoint arborescences).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), p.33 (PDF p.36): "Let G = (V, E, c) be an n-vertex directed graph with
integer edge costs in [−W, W], and let k ⩾ 1. There exist the following sensitivity oracles that, for
any s ∈ V and any U ∈ E^f, return the corresponding outputs on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O((kn)^ω) | O(k²n²) | O(f^ω + f²k²) | Whether G + U has k-disjoint s-rooted arborescences |
| Weighted | Õ(W(kn)³) | O(W(kn)³ log n) | Õ(Wkn · (f^ω + f²k²)) | Min total cost of such k-arborescences |

§6.1, p.32: "A valid z-rooted spanning arborescence in H is a set of N − 1 edges forming a spanning
tree in the underlying undirected graph, where every vertex v ∈ V_H ∖ {z} has exactly one incoming
edge, and z has no incoming edges."

**Formalization Note.**
* Machine and oracle semantics: the base randomized word RAM; `P` reads `encodeWith G [n, k, f, W]`,
  `Q` reads only the stored string and `[s] ++ U.encode`. `ω = omega ℂ`; `O(x^ω)` is `C x^{ω+τ}`
  for every `τ > 0`; `Õ(X)` is `C X (log₂(Z + 2))^K`, `Z` the sum of the parameters in `X`.
* Space: `O(k²n²)` (no `log n`) counts words, `C k²n² w` bits; `O(W(kn)³ log n)` counts bits.
* With high probability: for every `c > 0` each fixed query errs with probability at most `n^{−c}`.
* Instances: `n ≥ 2`, `k ≥ 1`, `f ≥ 1`, `W ≥ 1`, costs in `[−W, W]`; queries: any root `s` and any
  update set of at most `f` insertions and deletions with inserted costs in `[−W, W]`; `G + U` is a
  multigraph.
* Outputs: word `0` is `1` iff `G + U` has `k` pairwise edge-disjoint `s`-rooted spanning
  arborescences; the weighted oracle, when they exist, also returns in word `1` (signed) the least
  total cost of such a family. -/
theorem theorem_6_3 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n), 2 ≤ n → 1 ≤ k → 1 ≤ f → 1 ≤ W →
        G.CostsBounded W → ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), k, f, W]
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let Qs : Set (Fin n × Update n) := {q | G.ValidUpdate f W q.2}
          let enc : Fin n × Update n → List ℤ := fun q => [((q.1 : ℕ) : ℤ)] ++ q.2.encode
          let base : ℝ := (f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2
          let feas : Fin n × Update n → Prop :=
            fun q => HasKDisjoint (G.plus q.2) (IsArborescence (G.plus q.2) q.1) k
          let minC : Fin n × Update n → WithTop ℤ :=
            fun q => minKDisjointCost (G.plus q.2) (IsArborescence (G.plus q.2) q.1) k
          -- Decision
          O₁.Serves w inp ⌊C * kn ^ (ω + τ)⌋₊ (C * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * w) Qs enc
            ⌊C * base⌋₊ (fun q mQ => Answers (feas q) (minC q) false mQ) err ∧
          -- Weighted
          O₂.Serves w inp ⌊C * W * kn ^ 3 * Real.logb 2 ((W + k + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (C * W * kn ^ 3 * Real.logb 2 n) Qs enc
            ⌊C * W * kn * base * Real.logb 2 ((W + k + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun q mQ => Answers (feas q) (minC q) true mQ) err := by sorry

end MatroidSensOracle.Supplement
