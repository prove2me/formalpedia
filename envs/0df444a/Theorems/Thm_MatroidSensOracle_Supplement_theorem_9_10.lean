-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_10
-- name    : MatroidSensOracle.Supplement.theorem_9_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:24:53.206022+00:00
-- url     : https://prove2.me/theorems/76bba70a-a83c-4b24-aab2-41eb02e342ce
-- title:
--   Theorem 9.10 (subset forest packing / arboricity $\le k$)
-- statement:
--   Let $k\ge1$ and let $G=(V,E)$ be an undirected graph on $n$ vertices with a susceptible set $E_Q$ of $m^\star\ge1$ pairs (possibly not in $E$); let $E_0=E\cup E_Q$. For every $c>0$ and $\tau>0$ there are constants $C,b$ and an oracle on the randomized word RAM with preprocessing
--   $$C\bigl(k^2|E_0|+(m^\star)^2(kn)^{\omega-2+\tau}+(kn)^{\omega+\tau}\bigr),$$
--   space $C(m^\star)^2$ words and query time $Cf^{\omega+\tau}$ that, for every $U\subseteq E_Q$ with $|U|\le f$ after whose toggling $G+U$ has at most $k(n-1)$ edges, decides whether $G+U$ partitions into $k$ forests; each fixed query is answered wrongly with probability at most $n^{-c}$.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: a susceptible set E_Q (which may include edges not currently in E); updates U ⊆ E_Q → a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E (toggles); reason: the §9 subset model; insertions and deletions are exactly the toggles of susceptible pairs
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.10, p.52 (PDF p.55)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.10 (subset forest packing / arboricity).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), p.52 (PDF p.55): "Let k ⩾ 1 be an integer, and G = (V, E) be an
undirected graph with n vertices and a susceptible edge set E_Q of size m★. Let E_0 = E ∪ E_Q. There
exists a subset sensitivity oracle that, for any set of edge insertions or deletions U ⊆ E_Q of size
at most f (where the updated active edge count m_curr ⩽ k(n − 1)), answers queries on G + U with high
probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O(k²|E_0| + (m★)²(kn)^{ω−2} + (kn)^ω) | O((m★)²) | O(f^ω) | Whether G + U partitions into k forests |

§9.4.4, p.52: "Let E_Q be a susceptible set of size m★ (which may include edges not currently in E)".

**Formalization Note.**
* Subset model as in `theorem_9_1` (toggles); undirected graphs and pairs of `E_Q` as in
  `theorem_9_8`; `m★ = |E_Q| ≥ 1`. Queries: `U ⊆ E_Q`, `|U| ≤ f`, with at most `k(n − 1)` edges in
  `G + U`.
* Machine, oracle semantics, asymptotics, space units (`O((m★)²)` in words) and "with high
  probability" as in `theorem_9_1`. `P` reads `encodeSubset G [n, k, f] E_Q ∅` (costs ignored), `Q`
  reads `pairWords U`.
* Instances: `n ≥ 2`, `k ≥ 1`, `f ≥ 1`. Output as in `theorem_6_10`. -/
theorem theorem_9_10 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (b : ℕ) (O : Oracle),
      ∀ (n k f : ℕ) (G : InputGraph n) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ k → 1 ≤ f → G.Undirected → (∀ e ∈ EQ, e.1 < e.2) → 1 ≤ EQ.card →
        ∀ w : ℕ, b * (Nat.log 2 (n + k + f + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let kn : ℝ := (k : ℝ) * n
          let ms : ℝ := EQ.card
          let E0 : ℝ := (G.E ∪ EQ).card
          O.Serves w (encodeSubset G [(n : ℤ), k, f] EQ ∅)
            ⌊C * ((k : ℝ) ^ 2 * E0 + ms ^ 2 * kn ^ (ω - 2 + τ) + kn ^ (ω + τ))⌋₊ (C * ms ^ 2 * w)
            {U | U ⊆ EQ ∧ U.card ≤ f ∧ (G.plus (G.toggle U)).m ≤ k * (n - 1)} pairWords
            ⌊C * (f : ℝ) ^ (ω + τ)⌋₊
            (fun U mQ => ((mQ 0).toNat = 1 ↔ PartitionsIntoForests (G.plus (G.toggle U)) k))
            ((n : ℝ) ^ (-c)) := by sorry

end MatroidSensOracle.Supplement
