-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_12
-- name    : MatroidSensOracle.Supplement.theorem_9_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:25:52.384349+00:00
-- url     : https://prove2.me/theorems/d02b39eb-36b7-4faf-a7b6-d30efe631696
-- title:
--   Theorem 9.12 (subset $\alpha$-factor oracles, $\alpha\le k$): existence and min-cost
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$, degree bounds $\alpha:V\to\{1,\dots,k\}$, and a susceptible set $E_Q$ of $m^\star\ge1$ pairs. Queries are $U\subseteq E_Q$ with $|U|\le f$, toggling their pairs.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Existence:** preprocessing $C\bigl((m^\star)^2(kn)^{\omega-2+\tau}+(kn)^{\omega+\tau}\bigr)$, space $C(m^\star)^2$ words, query $Cf^{\omega+\tau}$; output whether $G+U$ has an $\alpha$-factor.
--   2. **Min-cost:** preprocessing $\tilde O\bigl(W(m^\star)^2(kn)^{\omega-1}+W(kn)^3\bigr)$, space $\tilde O(Wkn(m^\star)^2)$ bits, query $\tilde O(Wknf^{\omega})$; output the cost of a min-cost $\alpha$-factor of $G+U$ (or that none exists).
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - generalization: a susceptible edge set E_Q of G (subset α-factor setting) → E_Q any set of pairs; a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E; reason: the §9 subset model allows edges not currently in E; E_Q ⊆ E is the special case of deletions
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - generalization: for any update set U with f = |U| → every update set U with |U| ≤ f; reason: contains every U with |U| = f; the oracle is built for the budget f
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1, W ≥ 1, α(v) ≥ 1, costs on E ∪ E_Q in [−W, W]; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.12, pp.53–54 (PDF pp.56–57)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.12 (subset `α`-factors, `α ⩽ k`).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), pp.53–54 (PDF pp.56–57): "Let G = (V, E, c) be an undirected graph with
integer edge costs in [−W, W], degree bounds α ⩽ k, and a susceptible edge set E_Q of size m★. Then
there exist the following subset sensitivity oracles that, for any update set U ⊆ E_Q with f = |U|,
answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Existence | O((m★)²(kn)^{ω−2} + (kn)^ω) | O((m★)²) | O(f^ω) | Whether G + U has an α-factor |
| Min-Cost | Õ(W(m★)²(kn)^{ω−1} + W(kn)³) | Õ(Wkn(m★)²) | Õ(Wknf^ω) | Weight of a min-cost α-factor of G + U |

**Formalization Note.**
* Subset model as in `theorem_9_1` (toggles; the susceptible pairs may lie outside `E`, as in §9.1);
  undirected graphs and pairs of `E_Q` as in `theorem_9_8`; `m★ = |E_Q| ≥ 1`; `α(v) ∈ {1, …, k}`.
  The oracle is built for a budget `f` and answers every `U ⊆ E_Q` with `|U| ≤ f`, which contains
  those with `|U| = f`.
* Machine, oracle semantics, asymptotics, space units and "with high probability" as in
  `theorem_9_1`. `P` reads `encodeSubset G [n, k, f, W] E_Q ∅ ++ α`, `Q` reads `pairWords U`.
* Instances: `n ≥ 2`, `k ≥ 1`, `f ≥ 1`, `W ≥ 1`, costs on `E ∪ E_Q` in `[−W, W]`. Outputs as in
  `theorem_8_3`. -/
theorem theorem_9_12 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n) (α : Fin n → ℕ) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ k → 1 ≤ f → 1 ≤ W → G.Undirected → (∀ e ∈ EQ, e.1 < e.2) → 1 ≤ EQ.card →
        G.CostsBoundedOn EQ W → (∀ v, 1 ≤ α v ∧ α v ≤ k) →
        ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), k, f, W] EQ ∅ ++ List.ofFn fun v => ((α v : ℕ) : ℤ)
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let ms : ℝ := EQ.card
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ f}
          let H : Finset (Fin n × Fin n) → CostMultigraph (Fin n) := fun U => G.plus (G.toggle U)
          let lgS : ℝ := Real.logb 2 ((W + k + n + EQ.card : ℕ) + 2 : ℝ)
          -- Existence
          O₁.Serves w inp ⌊C * (ms ^ 2 * kn ^ (ω - 2 + τ) + kn ^ (ω + τ))⌋₊ (C * ms ^ 2 * w) Qs pairWords
            ⌊C * (f : ℝ) ^ (ω + τ)⌋₊
            (fun U mQ => Answers (HasFactor (H U) α) (minFactorCost (H U) α) false mQ) err ∧
          -- Min-Cost
          O₂.Serves w inp ⌊C * (W * ms ^ 2 * kn ^ (ω - 1 + τ) + W * kn ^ 3) * lgS ^ K⌋₊
            (C * W * kn * ms ^ 2 * lgS ^ K) Qs pairWords
            ⌊C * W * kn * (f : ℝ) ^ (ω + τ) * Real.logb 2 ((W + k + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (HasFactor (H U) α) (minFactorCost (H U) α) true mQ) err := by sorry

end MatroidSensOracle.Supplement
