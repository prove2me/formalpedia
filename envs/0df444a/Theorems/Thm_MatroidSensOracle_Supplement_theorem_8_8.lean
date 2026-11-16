-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_8_8
-- name    : MatroidSensOracle.Supplement.theorem_8_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:19:24.154207+00:00
-- url     : https://prove2.me/theorems/46bf6f40-40ab-43a2-9bbc-32c1a374d2a5
-- title:
--   Theorem 8.8 ($\alpha$-factor oracles for arbitrary $\alpha$): existence with $O((fn)^\omega+T_\alpha)$ preprocessing, min-cost
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex undirected graph with integer edge costs in $[-W,W]$ and arbitrary degree bounds $\alpha:V\to\mathbb Z_{>0}$. Let $T_\alpha$ be the running time of an algorithm that finds an $\alpha$-factor of $G$ or reports that none exists [5, 40].
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K$ such that for every such algorithm, with running time $T_\alpha$ on the instance, there are two oracles on the randomized word RAM answering every fixed query (a set $U$ of at most $f$ edge insertions and deletions) wrongly with probability at most $n^{-c}$:
--
--   1. **Existence:** preprocessing $C\bigl((fn)^{\omega+\tau}+T_\alpha\bigr)$, space $Cf^2n^2$ words, query $Cf^4$; output whether $G+U$ has an $\alpha$-factor.
--   2. **Min-cost:** preprocessing $\tilde O(W(fn)^3)$, space $CW(fn)^3\log_2 n$ bits, query $\tilde O(Wnf^5)$; output the cost of a min-cost $\alpha$-factor of $G+U$ (or that none exists).
--
--   The bounds do not depend on $\max_v\alpha(v)$.
--
--   **Formalization Note** No hypothesis that $G$ itself has an $\alpha$-factor is made, as printed; the min-cost row has no $T_\alpha$ term, as printed.
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
--   - generalization: T_α, the time of an α-factor algorithm [5, 40] → for every word-RAM program A that finds an α-factor of an undirected graph or reports that none exists within TA(input) steps, existence preprocessing within C·(printed term + TA), C and K independent of A; reason: specializes to the paper's claim with A the algorithm of [5, 40]
--   - encoding: word size for arbitrary α → the word width covers log₂ of Σ α(v) as well; reason: the α(v) are input numbers
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1, W ≥ 1, α(v) ≥ 1; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 8.8, p.44 (PDF p.47)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 8.8 (`α`-factors, arbitrary `α`).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held
version, sha256 0de50841…), p.44 (PDF p.47): "Let G = (V, E, c) be an undirected graph with integer
edge costs in [−W, W] and arbitrary degree bounds α. Then there exist the following sensitivity
oracles that, for any update set U with f = |U|, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Existence | O((fn)^ω + T_α) | O(f²n²) | O(f⁴) | Whether G + U has an α-factor |
| Min-Cost | Õ(W(fn)³) | O(W(fn)³ log n) | Õ(Wnf⁵) | Weight of a min-cost α-factor of G + U |

p.45 (PDF p.48): "finding the α-factor of G takes O(T_α) time [5, 40]".

**Formalization Note.**
* `T_α` is read parametrically: for every word-RAM program `A` that finds an `α`-factor of an
  undirected graph or reports that none exists (`FactorAlgorithm A bA TA`, within
  `TA (factorInput G α)` steps), the existence oracle's preprocessing time is at most
  `C ((fn)^{ω+τ} + TA (factorInput G α))`; `C` and `K` do not depend on `A`. The min-cost row has no
  `T_α` term, as printed. No hypothesis that `G` has an `α`-factor is made (none is printed).
* Machine, oracle semantics, `ω = omega ℂ`, `O(x^ω)`, `Õ` and "with high probability" as in
  `theorem_6_3`. Space `O(f²n²)` counts words (`C f²n² w` bits), `O(W(fn)³ log n)` bits. `P` reads
  `encodeWith G [n, f, W] ++ α`, `Q` reads `U.encode`.
* Undirected graphs as in `theorem_6_6`; `α(v) ≥ 1`. Queries: every update set of at most `f`
  insertions and deletions (inserted costs in `[−W, W]`), which contains those with `|U| = f`.
* Outputs as in `theorem_8_3`. -/
theorem theorem_8_8 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K : ℕ),
      ∀ (A : List Instr) (bA : ℕ) (TA : List ℤ → ℝ), FactorAlgorithm A bA TA →
      ∃ (b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n) (α : Fin n → ℕ), 2 ≤ n → 1 ≤ f → 1 ≤ W →
        G.Undirected → G.CostsBounded W → (∀ v, 1 ≤ α v) →
        ∀ w : ℕ, b * (Nat.log 2 (n + f + W + ∑ v, α v + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeWith G [(n : ℤ), f, W] ++ List.ofFn fun v => ((α v : ℕ) : ℤ)
          let err : ℝ := (n : ℝ) ^ (-c)
          let fn : ℝ := (f : ℝ) * n
          let Qs : Set (Update n) := {U | G.ValidU f W U}
          -- Existence
          O₁.Serves w inp ⌊C * (fn ^ (ω + τ) + TA (factorInput G α))⌋₊
            (C * (f : ℝ) ^ 2 * (n : ℝ) ^ 2 * w) Qs Update.encode ⌊C * (f : ℝ) ^ 4⌋₊
            (fun U mQ => Answers (HasFactor (G.plus U) α) (minFactorCost (G.plus U) α) false mQ) err ∧
          -- Min-Cost
          O₂.Serves w inp ⌊C * W * fn ^ 3 * Real.logb 2 ((W + f + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (C * W * fn ^ 3 * Real.logb 2 n) Qs Update.encode
            ⌊C * W * n * (f : ℝ) ^ 5 * Real.logb 2 ((W + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => Answers (HasFactor (G.plus U) α) (minFactorCost (G.plus U) α) true mQ)
            err := by sorry

end MatroidSensOracle.Supplement
