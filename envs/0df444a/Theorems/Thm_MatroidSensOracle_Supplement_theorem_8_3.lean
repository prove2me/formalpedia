-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_8_3
-- name    : MatroidSensOracle.Supplement.theorem_8_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:17:37.8252+00:00
-- url     : https://prove2.me/theorems/ab89be62-a334-4a15-be9e-01ca45d73b22
-- title:
--   Theorem 8.3 ($\alpha$-factor existence and min-cost oracles, degree bounds $\alpha\le k$)
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$ and let $\alpha:V\to\{1,\dots,k\}$. An **$\alpha$-factor** is a set of edges in which every vertex $v$ has degree exactly $\alpha(v)$. Queries are sets $U$ of at most $f$ edge insertions and deletions.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Existence:** preprocessing $C(kn)^{\omega+\tau}$, space $Ck^2n^2$ words, query $C(f^{\omega+\tau}+f^2k^2)$; output whether $G+U$ has an $\alpha$-factor.
--   2. **Min-cost:** preprocessing $\tilde O(W(kn)^3)$, space $CW(kn)^3\log_2 n$ bits, query $\tilde O\bigl(Wnk\,(f^{\omega}+f^2k^2)\bigr)$; output the cost of a min-cost $\alpha$-factor of $G+U$ (or that none exists).
--
--   With $\alpha\equiv1$ these are perfect-matching sensitivity oracles.
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
--   - generalization: for any update set U with f = |U| → every update set U with |U| ≤ f; reason: contains every U with |U| = f; the oracle is built for the budget f
--   - encoding: updates that change costs (§8.2) → a cost change is a deletion followed by an insertion; reason: the theorem's update sets consist of insertions and deletions; within constant factors of f
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1, W ≥ 1, α(v) ≥ 1 (α : V → Z+); reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 8.3, p.41 (PDF p.44)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 8.3 (`α`-factors, `α ⩽ k`).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version,
sha256 0de50841…), p.41 (PDF p.44): "Let G = (V, E, c) be an undirected graph with integer edge costs
in [−W, W] and degree bounds α ⩽ k. Then there exist the following sensitivity oracles that, for any
update set U with f = |U|, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Existence | O((kn)^ω) | O(k²n²) | O(f^ω + f²k²) | Whether G + U has an α-factor |
| Min-Cost | Õ(W(kn)³) | O(W(kn)³ log n) | Õ(Wnk · (f^ω + f²k²)) | Weight of a min-cost α-factor of G + U |

§8, p.39 (PDF p.42): "Let α : V → Z+ be a function assigning a degree bound to each vertex in V. […]
we define a (perfect) α-factor as a subgraph H of G such that every vertex v ∈ V has degree exactly
α(v) in H."

**Formalization Note.**
* Machine, oracle semantics, `ω = omega ℂ`, `O(x^ω)`, `Õ`, space units (`O(k²n²)` in words,
  `O(W(kn)³ log n)` in bits) and "with high probability" as in `theorem_6_3`. `P` reads
  `encodeWith G [n, k, f, W] ++ α`, `Q` reads `U.encode`.
* Undirected graphs as in `theorem_6_6`; `α(v) ∈ {1, …, k}` for every `v`. The oracle is built for a
  budget `f` and answers every update set of at most `f` insertions and deletions (inserted costs in
  `[−W, W]`); this contains the queries with `|U| = f`. A cost change is a deletion and an insertion.
* An `α`-factor of the multigraph `G + U` is a set of edges in which every `v` has degree `α(v)`.
* Outputs: word `0` is `1` iff `G + U` has an `α`-factor; the min-cost oracle, when one exists,
  returns in word `1` (signed) the least cost of an `α`-factor. -/
theorem theorem_8_3 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n) (α : Fin n → ℕ), 2 ≤ n → 1 ≤ k → 1 ≤ f → 1 ≤ W →
        G.Undirected → G.CostsBounded W → (∀ v, 1 ≤ α v ∧ α v ≤ k) →
        ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), k, f, W] ++ List.ofFn fun v => ((α v : ℕ) : ℤ)
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let Qs : Set (Update n) := {U | G.ValidU f W U}
          let base : ℝ := (f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * (k : ℝ) ^ 2
          -- Existence
          O₁.Serves w inp ⌊C * kn ^ (ω + τ)⌋₊ (C * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * w) Qs Update.encode
            ⌊C * base⌋₊
            (fun U mQ => Answers (HasFactor (G.plus U) α) (minFactorCost (G.plus U) α) false mQ) err ∧
          -- Min-Cost
          O₂.Serves w inp ⌊C * W * kn ^ 3 * Real.logb 2 ((W + k + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (C * W * kn ^ 3 * Real.logb 2 n) Qs Update.encode
            ⌊C * W * n * k * base * Real.logb 2 ((W + n + k + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (HasFactor (G.plus U) α) (minFactorCost (G.plus U) α) true mQ)
            err := by sorry

end MatroidSensOracle.Supplement
