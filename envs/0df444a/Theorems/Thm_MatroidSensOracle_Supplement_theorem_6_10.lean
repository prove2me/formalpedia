-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_6_10
-- name    : MatroidSensOracle.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:15:52.867287+00:00
-- url     : https://prove2.me/theorems/03c10502-349b-46ab-b81e-1b42cbf4d90b
-- title:
--   Theorem 6.10 (forest packing / arboricity $\le k$), for updates keeping at most $k(n-1)$ edges
-- statement:
--   Let $G=(V,E)$ be an undirected graph on $n$ vertices and let $k\ge1$. For every $c>0$ and $\tau>0$ there are constants $C,b$ and an oracle on the randomized word RAM with preprocessing $C(kn)^{\omega+\tau}$, space $Ck^2n^2$ words and query time $C(f^{\omega+\tau}+f^2k)$ that, for every set $U$ of at most $f$ edge insertions and deletions after which $G+U$ has at most $k(n-1)$ edges, decides whether the edge set of $G+U$ partitions into $k$ forests; each fixed query is answered wrongly with probability at most $n^{-c}$.
--
--   By Nash-Williams' theorem this decides whether the arboricity of $G+U$ is at most $k$.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 6.10, pp.35–36 (PDF pp.38–39)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 6.10 (forest packing / arboricity).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), pp.35–36 (PDF pp.38–39): "Let G = (V, E) be an undirected graph with n
vertices, and k ⩾ 1. There exists a sensitivity oracle that, given any set of updates U consisting of
at most f edge insertions or deletions (such that the updated active edge count m_curr remains
bounded by k(n−1)), answers queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O((kn)^ω) | O(k²n²) | O(f^ω + f²k) | Whether G + U partitions into k forests |

**Formalization Note.**
* Machine, oracle semantics, `ω = omega ℂ`, `O(x^ω)` and "with high probability" as in
  `theorem_6_3`. `P` reads `encodeWith G [n, k, f]` (the costs in the encoding are ignored), `Q`
  reads `U.encode`. The space `O(k²n²)` (no `log n`) counts words, `C k²n² w` bits.
* Undirected graphs as in `theorem_6_6`; `n ≥ 2`, `k ≥ 1`, `f ≥ 1`. Queries: at most `f` insertions
  and deletions (`F ⊆ E`, inserted edges join distinct vertices) after which `G + U` has at most
  `k(n − 1)` edges.
* Output: word `0` is `1` iff the edge set of `G + U` splits into `k` forests. -/
theorem theorem_6_10 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (b : ℕ) (O : Oracle),
      ∀ (n k f : ℕ) (G : InputGraph n), 2 ≤ n → 1 ≤ k → 1 ≤ f → G.Undirected →
        ∀ w : ℕ, b * (Nat.log 2 (n + k + f + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          O.Serves w (encodeWith G [(n : ℤ), k, f]) ⌊C * ((k : ℝ) * n) ^ (ω + τ)⌋₊
            (C * (k : ℝ) ^ 2 * (n : ℝ) ^ 2 * w)
            {U | G.ValidUPlain f U ∧ (G.plus U).m ≤ k * (n - 1)} Update.encode
            ⌊C * ((f : ℝ) ^ (ω + τ) + (f : ℝ) ^ 2 * k)⌋₊
            (fun U mQ => ((mQ 0).toNat = 1 ↔ PartitionsIntoForests (G.plus U) k)) ((n : ℝ) ^ (-c)) := by sorry

end MatroidSensOracle.Supplement
