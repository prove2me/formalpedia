-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_9
-- name    : MatroidSensOracle.Supplement.theorem_9_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:24:12.064124+00:00
-- url     : https://prove2.me/theorems/8ee2ed76-7fbe-4652-b5c5-ea085e642100
-- title:
--   Theorem 9.9 (subset colorful spanning trees): decision and weighted oracles
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$ whose edges, and the pairs of a susceptible set $E_Q$ of $m^\star\ge1$ pairs (possibly not in $E$), each carry one of $n-1$ colors. Queries are $U\subseteq E_Q$ with $|U|\le f$; a query deletes the pairs of $U$ in $E$ and inserts the others with their assigned colors and costs.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Decision:** preprocessing $C\bigl((m^\star)^2n^{\omega-2+\tau}+n^{\omega+\tau}\bigr)$, space $C(m^\star)^2$ words, query $Cf^{\omega+\tau}$; output whether $G+U$ has a colorful spanning tree.
--   2. **Weighted:** preprocessing $\tilde O\bigl(W(m^\star)^2n^{\omega-1}+Wn^{\omega+1}\bigr)$, space $\tilde O(Wn(m^\star)^2)$ bits, query $\tilde O(Wnf^{\omega})$; output the minimum cost of a colorful spanning tree (or that none exists).
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: no success probability printed → for every c > 0 each fixed query errs with probability at most n^{−c}; reason: §9 lifts §6, whose Theorem 6.8 holds with high probability; the proof invokes the randomized Theorem 3.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: a susceptible set E_Q (which may include edges not currently in E); updates U ⊆ E_Q → a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E (toggles); reason: the §9 subset model; insertions and deletions are exactly the toggles of susceptible pairs
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - reading: costs (not repeated in the theorem) → costs in [−W, W] on E ∪ E_Q; reason: the standing assumption of §6.3
--   - generalization: exactly n − 1 nonempty color classes → a coloring χ : V × V → Fin (n − 1); a class may be empty; reason: contains the printed case
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1, W ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.9, pp.51–52 (PDF pp.54–55)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.9 (subset colorful spanning trees).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), pp.51–52 (PDF pp.54–55): "Let G = (V, E, c) be an undirected colored graph
with a susceptible edge set E_Q of size m★. Then there exist the following subset sensitivity oracles
for any set of updates U ⊆ E_Q of size at most f:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O((m★)²n^{ω−2} + n^ω) | O((m★)²) | O(f^ω) | Whether G + U has a colorful spanning tree |
| Weighted | Õ(W(m★)²n^{ω−1} + Wn^{ω+1}) | Õ(Wn(m★)²) | Õ(Wnf^ω) | Min cost of a colorful spanning tree |

§9.4.3, p.51: "confine updates to a fixed susceptible set E_Q of size m★ (which may include edges not
currently in E, each assigned to one of the n − 1 color classes)".

**Formalization Note.**
* No probability is printed; as in §6.3 (Theorem 6.8, which this theorem lifts) the oracles are read
  as answering with high probability: for every `c > 0` each fixed query errs with probability at most
  `n^{−c}`.
* Colours `χ : V × V → Fin (n − 1)` on `E ∪ E_Q` as in `theorem_6_8`; a query `U ⊆ E_Q`, `|U| ≤ f`,
  deletes `U ∩ E` and inserts `U ∖ E` with its cost and colour `χ` (`ctoggle`). Costs on `E ∪ E_Q`
  lie in `[−W, W]` (§6.3). Undirected graphs as in `theorem_9_8`; `m★ = |E_Q| ≥ 1`.
* Machine, oracle semantics, asymptotics and space units as in `theorem_9_1`. `P` reads
  `encodeColored G χ [n, f, W] E_Q`, `Q` reads `pairWords U`.
* Instances: `n ≥ 2`, `f ≥ 1`, `W ≥ 1`. Outputs as in `theorem_6_8`. -/
theorem theorem_9_9 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n) (χ : Fin n × Fin n → Fin (n - 1)) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ f → 1 ≤ W → G.Undirected → (∀ e ∈ EQ, e.1 < e.2) → 1 ≤ EQ.card →
        G.CostsBoundedOn EQ W → ∀ w : ℕ, b * (Nat.log 2 (n + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeColored G χ [(n : ℤ), f, W] EQ
          let err : ℝ := (n : ℝ) ^ (-c)
          let ms : ℝ := EQ.card
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ f}
          let feas : Finset (Fin n × Fin n) → Prop := fun U => HasColorfulTree (cEdges G χ (ctoggle G χ U))
          let minC : Finset (Fin n × Fin n) → WithTop ℤ :=
            fun U => minColorfulCost (cEdges G χ (ctoggle G χ U))
          let lgS : ℝ := Real.logb 2 ((W + n + EQ.card : ℕ) + 2 : ℝ)
          -- Decision
          O₁.Serves w inp ⌊C * (ms ^ 2 * (n : ℝ) ^ (ω - 2 + τ) + (n : ℝ) ^ (ω + τ))⌋₊ (C * ms ^ 2 * w)
            Qs pairWords ⌊C * (f : ℝ) ^ (ω + τ)⌋₊
            (fun U mQ => Answers (feas U) (minC U) false mQ) err ∧
          -- Weighted
          O₂.Serves w inp
            ⌊C * (W * ms ^ 2 * (n : ℝ) ^ (ω - 1 + τ) + W * (n : ℝ) ^ (ω + 1 + τ)) * lgS ^ K⌋₊
            (C * W * n * ms ^ 2 * lgS ^ K) Qs pairWords
            ⌊C * W * n * (f : ℝ) ^ (ω + τ) * Real.logb 2 ((W + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (feas U) (minC U) true mQ) err := by sorry

end MatroidSensOracle.Supplement
