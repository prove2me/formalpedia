-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_13
-- name    : MatroidSensOracle.Supplement.theorem_9_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:26:18.125204+00:00
-- url     : https://prove2.me/theorems/6fafa87f-1324-42da-abb2-cd53d1aea587
-- title:
--   Theorem 9.13 (subset $\alpha$-factor oracles, arbitrary $\alpha$): existence with $T_\alpha$, min-cost
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$, arbitrary degree bounds $\alpha:V\to\mathbb Z_{>0}$, and a susceptible set $E_Q$ of $m^\star\ge1$ pairs. Queries are $U\subseteq E_Q$ with $|U|\le f$, toggling their pairs. Let $T_\alpha$ be as in Theorem 8.8.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K$ such that for every $\alpha$-factor algorithm with running time $T_\alpha$ there are two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Existence:** preprocessing $C\bigl((m^\star)^2(fn)^{\omega-2+\tau}+(fn)^{\omega+\tau}+T_\alpha\bigr)$, space $C(m^\star)^2$ words, query $Cf^{\omega+\tau}$; output whether $G+U$ has an $\alpha$-factor.
--   2. **Min-cost:** preprocessing $\tilde O\bigl(W(m^\star)^2(fn)^{\omega-1}+W(fn)^3\bigr)$, space $\tilde O(Wfn(m^\star)^2)$ bits, query $\tilde O(Wnf^{\omega+1})$; output the cost of a min-cost $\alpha$-factor of $G+U$ (or that none exists).
--
--   **Formalization Note** No hypothesis that $G$ has an $\alpha$-factor is made, as printed.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - generalization: a susceptible edge set E_Q of G → E_Q any set of pairs; a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E; reason: the §9 subset model allows edges not currently in E; E_Q ⊆ E is the special case
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - generalization: for any update set U with f = |U| → every update set U with |U| ≤ f; reason: contains every U with |U| = f; the oracle is built for the budget f
--   - generalization: T_α, the time of an α-factor algorithm [5, 40] → for every word-RAM program A that finds an α-factor of an undirected graph or reports that none exists within TA(input) steps, existence preprocessing within C·(printed term + TA), C and K independent of A; reason: specializes to the paper's claim with A the algorithm of [5, 40]
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: word size for arbitrary α → the word width covers log₂ of Σ α(v) as well; reason: the α(v) are input numbers
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1, W ≥ 1, α(v) ≥ 1, costs on E ∪ E_Q in [−W, W]; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.13, p.54 (PDF p.57)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.13 (subset `α`-factors, arbitrary `α`).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), p.54 (PDF p.57): "Let G = (V, E, c) be an undirected graph with
integer edge costs in [−W, W], arbitrary degree bounds α, and a susceptible edge set E_Q of size m★.
Then there exist the following subset sensitivity oracles that, for any update set U ⊆ E_Q with
f = |U|, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Existence | O((m★)²(fn)^{ω−2} + (fn)^ω + T_α) | O((m★)²) | O(f^ω) | Whether G + U has an α-factor |
| Min-Cost | Õ(W(m★)²(fn)^{ω−1} + W(fn)³) | Õ(Wfn(m★)²) | Õ(Wnf^{ω+1}) | Weight of a min-cost α-factor of G + U |

**Formalization Note.**
* `T_α` is read parametrically as in `theorem_8_8` (`FactorAlgorithm A bA TA`; `C`, `K` independent
  of `A`); the min-cost row has no `T_α` term, as printed; no hypothesis that `G` has an `α`-factor.
* Subset model, undirected graphs and pairs of `E_Q`, `m★ = |E_Q| ≥ 1`, and the reading of
  `f = |U|` as in `theorem_9_12`; `α(v) ≥ 1`.
* Machine, oracle semantics, asymptotics, space units and "with high probability" as in
  `theorem_9_1`. `P` reads `encodeSubset G [n, f, W] E_Q ∅ ++ α`, `Q` reads `pairWords U`; the word
  width covers `Σ α`.
* Instances: `n ≥ 2`, `f ≥ 1`, `W ≥ 1`, costs on `E ∪ E_Q` in `[−W, W]`. Outputs as in
  `theorem_8_3`. -/
theorem theorem_9_13 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K : ℕ),
      ∀ (A : List Instr) (bA : ℕ) (TA : List ℤ → ℝ), FactorAlgorithm A bA TA →
      ∃ (b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n) (α : Fin n → ℕ) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ f → 1 ≤ W → G.Undirected → (∀ e ∈ EQ, e.1 < e.2) → 1 ≤ EQ.card →
        G.CostsBoundedOn EQ W → (∀ v, 1 ≤ α v) →
        ∀ w : ℕ, b * (Nat.log 2 (n + f + W + ∑ v, α v + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), f, W] EQ ∅ ++ List.ofFn fun v => ((α v : ℕ) : ℤ)
          let err : ℝ := (n : ℝ) ^ (-c)
          let fn : ℝ := (f : ℝ) * n
          let ms : ℝ := EQ.card
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ f}
          let H : Finset (Fin n × Fin n) → CostMultigraph (Fin n) := fun U => G.plus (G.toggle U)
          let lgS : ℝ := Real.logb 2 ((W + f + n + EQ.card : ℕ) + 2 : ℝ)
          -- Existence
          O₁.Serves w inp ⌊C * (ms ^ 2 * fn ^ (ω - 2 + τ) + fn ^ (ω + τ) + TA (factorInput G α))⌋₊
            (C * ms ^ 2 * w) Qs pairWords ⌊C * (f : ℝ) ^ (ω + τ)⌋₊
            (fun U mQ => Answers (HasFactor (H U) α) (minFactorCost (H U) α) false mQ) err ∧
          -- Min-Cost
          O₂.Serves w inp ⌊C * (W * ms ^ 2 * fn ^ (ω - 1 + τ) + W * fn ^ 3) * lgS ^ K⌋₊
            (C * W * fn * ms ^ 2 * lgS ^ K) Qs pairWords
            ⌊C * W * n * (f : ℝ) ^ (ω + 1 + τ) * Real.logb 2 ((W + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (HasFactor (H U) α) (minFactorCost (H U) α) true mQ) err := by sorry

end MatroidSensOracle.Supplement
