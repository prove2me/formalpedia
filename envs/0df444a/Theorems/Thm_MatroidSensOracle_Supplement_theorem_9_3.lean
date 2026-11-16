-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_3
-- name    : MatroidSensOracle.Supplement.theorem_9_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:21:12.102698+00:00
-- url     : https://prove2.me/theorems/757b5494-4b4b-4fea-8bad-e099da6c10e6
-- title:
--   Theorem 9.3 (subset $(s,t)$-max-flow, nearest min-cut and min-cost max-flow oracles)
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex directed graph with $m$ edges, integer edge costs in $[-W,W]$, source $s$, sink $t\ne s$, and a susceptible set $E_Q$ of $m^\star\ge1$ pairs (possibly not in $E$). A query is $U\subseteq E_Q$ with $|U|\le f$, toggling its pairs.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and three oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Max-flow:** preprocessing $C\bigl(m^{1+\tau}+(m^\star)^2(fn)^{\omega-2+\tau}\bigr)$, space $C(m^\star)^2$ words, query $\tilde O(f^{\omega})$; output $\lambda_{G+U}(s,t)$.
--   2. **Nearest min-cut:** preprocessing $C((m^\star)^2+n^2)(fn)^{\omega-2+\tau}$, space $C((m^\star)^2+n^2)$ words, query $\tilde O(f^{\omega}n)$; output $\mathrm{NMC}_{G+U}(s,t)$.
--   3. **Min-cost flow:** preprocessing $\tilde O(m^{1+\tau}+W(m^\star)^2(fn)^{\omega-1+\tau})$, space $\tilde O(Wfn(m^\star)^2)$ bits, query $\tilde O(Wnf^{\omega+1})$; output the minimum cost of a maximum $(s,t)$-flow of $G+U$.
--
--   Compared with Theorem 5.5, the space depends on the number of susceptible edges instead of on $fn$.
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - generalization: a susceptible set E_Q ⊆ E; updates U ⊆ E_Q consisting of insertions and deletions → E_Q any set of pairs (with costs), possibly not in E; a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E; reason: §9.1: E_Q 'may include edges not currently in E'; the printed E_Q ⊆ E is the special case
--   - encoding: a susceptible set of size m★ → m★ = |E_Q| ≥ 1; reason: an O((m★)²) space bound is 0 at m★ = 0, where no oracle can answer; as in the base subset setting (1 ≤ m★)
--   - encoding: m^{1+o(1)} → C·m^{1+τ} for every τ > 0; reason: o(1) in an exponent
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, f ≥ 1, W ≥ 1, s ≠ t, costs on E ∪ E_Q in [−W, W]; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.3, p.47 (PDF p.50)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.3 (subset `(s, t)`-max-flow, nearest min-cut, min-cost max-flow).** Choudhary, Kumar,
Saggi, arXiv:2609.01283 (held version, sha256 0de50841…), p.47 (PDF p.50): "Let G = (V, E, c) be an
n-vertex directed graph with integer edge costs in [−W, W], with source s, sink t, and susceptible
set E_Q ⊆ E of size m★. Then there exist the following subset sensitivity oracles that, for any
U ∈ E_Q^f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Max-Flow | O(m^{1+o(1)} + (m★)²(fn)^{ω−2}) | O((m★)²) | Õ(f^ω) | λ_{G+U}(s, t) |
| Nearest Min-Cut | O(((m★)² + n²)(fn)^{ω−2}) | O((m★)² + n²) | Õ(f^ω n) | NMC_{G+U}(s, t) |
| Min-Cost Flow | Õ(m^{1+o(1)} + W(m★)²(fn)^{ω−1}) | Õ(Wfn(m★)²) | Õ(Wnf^{ω+1}) | Min-cost max-flow in G + U |

§9.1.2, p.47: "a susceptible edge set E_Q (which may include edges not currently in E)".

**Formalization Note.**
* Subset model as in `theorem_9_1` (`U ⊆ E_Q`, `|U| ≤ f`, toggles; `E_Q ⊆ E` is a special case).
  `m = |E|`, `m★ = |E_Q| ≥ 1`.
* Machine, oracle semantics, `ω = omega ℂ`, exponents `ω − 2`, `ω − 1` (`+ τ` for every `τ > 0`),
  `Õ`, space units and "with high probability" as in `theorem_9_1`; `m^{1+o(1)}` is `C m^{1+τ}` for
  every `τ > 0`. `P` reads `encodeSubset G [n, f, W, s, t] E_Q ∅`, `Q` reads `pairWords U`.
* Instances: `n ≥ 2`, `f ≥ 1`, `W ≥ 1`, `s ≠ t`, costs on `E ∪ E_Q` in `[−W, W]`.
* Outputs: word `0` is `λ_{G+U}(s, t)`; the low bits of words `0, …, n − 1` mark the source side of
  `NMC_{G+U}(s, t)`; word `0` (signed) is the least cost of an `(s, t)`-flow of value
  `λ_{G+U}(s, t)` in `G + U`. -/
theorem theorem_9_3 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ : Oracle),
      ∀ (n f W : ℕ) (G : InputGraph n) (s t : Fin n) (EQ : Finset (Fin n × Fin n)),
        2 ≤ n → 1 ≤ f → 1 ≤ W → s ≠ t → 1 ≤ EQ.card → G.CostsBoundedOn EQ W →
        ∀ w : ℕ, b * (Nat.log 2 (n + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), f, W, (s : ℕ), (t : ℕ)] EQ ∅
          let err : ℝ := (n : ℝ) ^ (-c)
          let fn : ℝ := (f : ℝ) * n
          let m : ℝ := (pairList n G.E).length
          let ms : ℝ := EQ.card
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ f}
          let H : Finset (Fin n × Fin n) → CostMultigraph (Fin n) := fun U => G.plus (G.toggle U)
          let lgf : ℝ := Real.logb 2 ((f : ℝ) + 2)
          -- Max-Flow
          O₁.Serves w inp ⌊C * (m ^ (1 + τ) + ms ^ 2 * fn ^ (ω - 2 + τ))⌋₊ (C * ms ^ 2 * w) Qs pairWords
            ⌊C * (f : ℝ) ^ (ω + τ) * lgf ^ K⌋₊
            (fun U mQ => (mQ 0).toNat = (H U).maxFlow s t) err ∧
          -- Nearest Min-Cut
          O₂.Serves w inp ⌊C * (ms ^ 2 + (n : ℝ) ^ 2) * fn ^ (ω - 2 + τ)⌋₊
            (C * (ms ^ 2 + (n : ℝ) ^ 2) * w) Qs pairWords
            ⌊C * (f : ℝ) ^ (ω + τ) * n * Real.logb 2 ((f + n : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => (H U).IsNearestMinCut s t (outSet mQ)) err ∧
          -- Min-Cost max-flow
          O₃.Serves w inp
            ⌊C * (m ^ (1 + τ) + W * ms ^ 2 * fn ^ (ω - 1 + τ)) *
              Real.logb 2 ((pairList n G.E).length + W + EQ.card + f + n + 2 : ℝ) ^ K⌋₊
            (C * W * fn * ms ^ 2 * Real.logb 2 ((W + f + n + EQ.card : ℕ) + 2 : ℝ) ^ K) Qs pairWords
            ⌊C * W * n * (f : ℝ) ^ (ω + 1 + τ) * Real.logb 2 ((W + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun U mQ => ((mQ 0).toInt : WithTop ℤ) = (H U).minCostFlow s t ((H U).maxFlow s t))
            err := by sorry

end MatroidSensOracle.Supplement
