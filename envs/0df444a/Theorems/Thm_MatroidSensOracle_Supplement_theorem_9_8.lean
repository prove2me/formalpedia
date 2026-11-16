-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_8
-- name    : MatroidSensOracle.Supplement.theorem_9_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:23:31.396954+00:00
-- url     : https://prove2.me/theorems/5595d29b-baf4-4d54-a8a0-590632fe9abe
-- title:
--   Theorem 9.8 (subset $k$ edge-disjoint spanning trees): decision and weighted oracles
-- statement:
--   Let $k\ge1$ and let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$ and a susceptible set $E_Q$ of $m^\star\ge1$ pairs (possibly not in $E$). Queries are $U\subseteq E_Q$ with $|U|\le f$, toggling their pairs.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Decision:** preprocessing $C\bigl((m^\star)^2(kn)^{\omega-2+\tau}+(kn)^{\omega+\tau}\bigr)$, space $C(m^\star)^2$ words, query $Cf^{\omega+\tau}$; output whether $G+U$ has $k$ edge-disjoint spanning trees.
--   2. **Weighted:** preprocessing $\tilde O\bigl(W(m^\star)^2(kn)^{\omega-1}+W(kn)^3\bigr)$, space $\tilde O(Wkn(m^\star)^2)$ bits, query $\tilde O(Wknf^{\omega})$; output their minimum total cost (or that none exist).
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: a susceptible set E_Q (which may include edges not currently in E); updates U ⊆ E_Q → a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E (toggles); reason: the §9 subset model; insertions and deletions are exactly the toggles of susceptible pairs
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1, W ≥ 1, costs on E ∪ E_Q in [−W, W]; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.8, p.51 (PDF p.54)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.8 (subset `k` edge-disjoint spanning trees).** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.51 (PDF p.54): "Let k ⩾ 1 be an integer, and
G = (V, E, c) be an n-vertex undirected graph with integer edge costs in [−W, W] and a susceptible
edge set E_Q of size m★. Then there exist the following subset sensitivity oracles that, for any set
of updates U ⊆ E_Q of size at most f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O((m★)²(kn)^{ω−2} + (kn)^ω) | O((m★)²) | O(f^ω) | Whether G + U has k edge-disjoint spanning trees |
| Weighted | Õ(W(m★)²(kn)^{ω−1} + W(kn)³) | Õ(Wkn · (m★)²) | Õ(Wkn · f^ω) | Min total cost of such k-spanning trees |

§9.4.2, p.51: "Let E_Q be a susceptible set of size m★ (which may include edges not currently in E)".

**Formalization Note.**
* Subset model as in `theorem_9_1` (toggles); undirected graphs as in `theorem_6_6`, and every pair of
  `E_Q` is written `(a, b)` with `a < b`. `m★ = |E_Q| ≥ 1`.
* Machine, oracle semantics, asymptotics, space units and "with high probability" as in
  `theorem_9_1`. `P` reads `encodeSubset G [n, k, f, W] E_Q ∅`, `Q` reads `pairWords U`.
* Instances: `n ≥ 2`, `k ≥ 1`, `f ≥ 1`, `W ≥ 1`, costs on `E ∪ E_Q` in `[−W, W]`. Outputs as in
  `theorem_6_6`. -/
theorem theorem_9_8 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ k → 1 ≤ f → 1 ≤ W → G.Undirected → (∀ e ∈ EQ, e.1 < e.2) → 1 ≤ EQ.card →
        G.CostsBoundedOn EQ W → ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), k, f, W] EQ ∅
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let ms : ℝ := EQ.card
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ f}
          let H : Finset (Fin n × Fin n) → CostMultigraph (Fin n) := fun U => G.plus (G.toggle U)
          let feas : Finset (Fin n × Fin n) → Prop := fun U => HasKDisjoint (H U) (IsSpanningTree (H U)) k
          let minC : Finset (Fin n × Fin n) → WithTop ℤ :=
            fun U => minKDisjointCost (H U) (IsSpanningTree (H U)) k
          let lgS : ℝ := Real.logb 2 ((W + k + n + EQ.card : ℕ) + 2 : ℝ)
          -- Decision
          O₁.Serves w inp ⌊C * (ms ^ 2 * kn ^ (ω - 2 + τ) + kn ^ (ω + τ))⌋₊ (C * ms ^ 2 * w) Qs pairWords
            ⌊C * (f : ℝ) ^ (ω + τ)⌋₊ (fun U mQ => Answers (feas U) (minC U) false mQ) err ∧
          -- Weighted
          O₂.Serves w inp ⌊C * (W * ms ^ 2 * kn ^ (ω - 1 + τ) + W * kn ^ 3) * lgS ^ K⌋₊
            (C * W * kn * ms ^ 2 * lgS ^ K) Qs pairWords
            ⌊C * W * kn * (f : ℝ) ^ (ω + τ) * Real.logb 2 ((W + k + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (feas U) (minC U) true mQ) err := by sorry

end MatroidSensOracle.Supplement
