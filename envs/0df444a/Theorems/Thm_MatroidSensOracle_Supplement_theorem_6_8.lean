-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_6_8
-- name    : MatroidSensOracle.Supplement.theorem_6_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:15:01.286252+00:00
-- url     : https://prove2.me/theorems/1b12f3ef-5174-4ac2-a856-71f6a7a8199b
-- title:
--   Theorem 6.8 (colorful spanning trees under insertions, deletions and color changes)
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$ whose edge set is partitioned into exactly $n-1$ color classes $C_1,\dots,C_{n-1}$. A **colorful spanning tree** is a spanning tree containing exactly one edge of each color class. Queries are sets $U$ of at most $f$ updates, each an edge insertion (with a cost and a color), an edge deletion, or a color change.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Decision:** preprocessing $Cn^{\omega+\tau}$, space $Cn^2\log_2 n$ bits, query $Cf^{\omega+\tau}$; output whether $G+U$ has a colorful spanning tree.
--   2. **Weighted:** preprocessing $\tilde O(Wn^3)$, space $CWn^3\log_2 n$ bits, query $\tilde O(Wnf^{\omega})$; output the minimum cost of a colorful spanning tree (or that none exists).
--
--   The colorful spanning tree is a common basis of the graphic and the color-partition matroid, so this is a 1-packing instance of the intersection framework.
--
--   **Formalization Note** A coloring is a map $\chi$ from vertex pairs to $\{0,\dots,n-2\}$ read on the edges; a color class may be empty (then no colorful tree exists).
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - reading: costs in [−W, W] (not repeated in the theorem) → costs in [−W, W] on E and on inserted edges; reason: the standing assumption of §6.3, p.34; the weighted row's bounds are in W
--   - generalization: E partitioned into exactly n − 1 color classes → a coloring χ : V × V → Fin (n − 1); a class may be empty; reason: contains every partition into n − 1 nonempty classes; an empty class only makes the answer negative
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1, W ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 6.8, p.35 (PDF p.38)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 6.8 (colorful spanning trees).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version,
sha256 0de50841…), p.35 (PDF p.38): "Let G = (V, E, c) be an undirected colored graph. Then there exist
the following sensitivity oracles that, given any set of updates U consisting of at most f edge
insertions, deletions, or color changes, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O(n^ω) | O(n² log n) | O(f^ω) | Whether G + U has a colorful spanning tree |
| Weighted | Õ(Wn³) | O(Wn³ log n) | Õ(Wnf^ω) | Min cost of a colorful spanning tree |

§6.3, p.34: "Let G = (V, E, c) be an undirected graph with n = |V| vertices and integer costs in
[−W, W]. The edge set E is partitioned into exactly n − 1 disjoint color classes […]. A colorful
spanning tree is a spanning tree of G containing exactly one edge from each color class."

**Formalization Note.**
* Machine, oracle semantics, `ω = omega ℂ`, `O(x^ω)`, `Õ` and "with high probability" as in
  `theorem_6_3`; both space bounds contain `log n` and count bits. `P` reads
  `encodeColored G χ [n, f, W] ∅`, `Q` reads `U.encode`.
* A colouring is `χ : V × V → Fin (n − 1)`, read on the edges: colour class `i` is `χ⁻¹(i) ∩ E`, so
  there are exactly `n − 1` classes; a class may be empty. Updates (`CUpdate`): insertions of edges
  with a cost in `[−W, W]` and a colour (joining distinct vertices), deletions of edges of `E`, and
  colour changes of surviving edges of `E`, each counting one, at most `f` in all.
* Undirected graphs as in `theorem_6_6`; `n ≥ 2`, `f ≥ 1`, `W ≥ 1`, costs in `[−W, W]`.
* Outputs: word `0` is `1` iff `G + U` has a colorful spanning tree; the weighted oracle, when one
  exists, returns in word `1` (signed) its least cost. -/
theorem theorem_6_8 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n) (χ : Fin n × Fin n → Fin (n - 1)), 2 ≤ n → 1 ≤ f → 1 ≤ W →
        G.Undirected → G.CostsBounded W → ∀ w : ℕ, b * (Nat.log 2 (n + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeColored G χ [(n : ℤ), f, W] ∅
          let err : ℝ := (n : ℝ) ^ (-c)
          let Qs : Set (CUpdate n) := {U | CUpdate.Valid G f W U}
          let feas : CUpdate n → Prop := fun U => HasColorfulTree (cEdges G χ U)
          let minC : CUpdate n → WithTop ℤ := fun U => minColorfulCost (cEdges G χ U)
          -- Decision
          O₁.Serves w inp ⌊C * (n : ℝ) ^ (ω + τ)⌋₊ (C * (n : ℝ) ^ 2 * Real.logb 2 n) Qs CUpdate.encode
            ⌊C * (f : ℝ) ^ (ω + τ)⌋₊ (fun U mQ => Answers (feas U) (minC U) false mQ) err ∧
          -- Weighted
          O₂.Serves w inp ⌊C * W * (n : ℝ) ^ 3 * Real.logb 2 ((W + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (C * W * (n : ℝ) ^ 3 * Real.logb 2 n) Qs CUpdate.encode
            ⌊C * W * n * (f : ℝ) ^ (ω + τ) * Real.logb 2 ((W + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (feas U) (minC U) true mQ) err := by sorry

end MatroidSensOracle.Supplement
