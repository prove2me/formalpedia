-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_6
-- name    : MatroidSensOracle.Supplement.theorem_9_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:22:42.177189+00:00
-- url     : https://prove2.me/theorems/b9bf9cc0-4437-4c6c-ab86-e1fc912279f5
-- title:
--   Theorem 9.6 (subset $k$-disjoint arborescences): decision and weighted oracles
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex directed graph with integer edge costs in $[-W,W]$, query roots $V_Q\subseteq V$, a susceptible set $E_Q$ of pairs (possibly not in $E$), and $k\ge1$; let $m^\star=|E_Q|+k|V_Q|$. A query is $(s,U)$ with $s\in V_Q$, $U\subseteq E_Q$, $|U|\le f$, toggling the pairs of $U$.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and two oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Decision:** preprocessing $C\bigl((m^\star)^2(kn)^{\omega-2+\tau}+(kn)^{\omega+\tau}\bigr)$, space $C(m^\star)^2$ words, query $C(f+k)^{\omega+\tau}$; output whether $G+U$ has $k$ edge-disjoint $s$-rooted spanning arborescences.
--   2. **Weighted:** preprocessing $\tilde O\bigl(W(m^\star)^2(kn)^{\omega-1}+W(kn)^3\bigr)$, space $\tilde O(Wkn(m^\star)^2)$ bits, query $\tilde O(Wkn(f+k)^{\omega})$; output the minimum total cost of such a family (or that none exists).
--
--   Differences from the source:
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - encoding: a susceptible set E_Q (which may include edges not currently in E); updates U ⊆ E_Q → a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E (toggles); reason: the §9 subset model; insertions and deletions are exactly the toggles of susceptible pairs
--   - encoding: the weighted oracle reports the minimum total cost → word 0 is 1 iff a feasible structure exists, and then word 1 (signed) is the minimum cost; reason: the oracle must also report nonexistence; this is the base Answers convention
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, k ≥ 1, f ≥ 1, W ≥ 1, costs on E ∪ E_Q in [−W, W]; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.6, p.50 (PDF p.53)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_MatroidSensOracle_MatroidOracle
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.6 (subset `k`-disjoint arborescences).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), p.50 (PDF p.53): "Let G = (V, E, c) be an n-vertex directed graph
with integer edge costs in [−W, W], query roots V_Q ⊆ V, and a susceptible set E_Q, and let k ⩾ 1.
Let m★ = |E_Q| + k|V_Q|. Then there exist the following subset sensitivity oracles that, for any
s ∈ V_Q and any U ∈ E_Q^f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Decision | O((m★)²(kn)^{ω−2} + (kn)^ω) | O((m★)²) | O((f + k)^ω) | Whether G + U has k-disjoint s-rooted arborescences |
| Weighted | Õ(W(m★)²(kn)^{ω−1} + W(kn)³) | Õ(Wkn(m★)²) | Õ(Wkn(f + k)^ω) | Min total cost of such k-arborescences |

§9.4.1, p.50: "a set of susceptible edges E_Q (which may include edges not currently in E) subject to
insertions or deletions."

**Formalization Note.**
* Subset model as in `theorem_9_1` (`U ⊆ E_Q`, `|U| ≤ f`, toggles). Machine, oracle semantics,
  asymptotics, space units (`O((m★)²)` in words, `Õ` in bits) and "with high probability" as in
  `theorem_9_1`. `P` reads `encodeSubset G [n, k, f, W] E_Q V_Q`, `Q` reads `[s] ++ pairWords U`.
* Instances: `n ≥ 2`, `k ≥ 1`, `f ≥ 1`, `W ≥ 1`, costs on `E ∪ E_Q` in `[−W, W]`.
* Arborescences and outputs as in `theorem_6_3`. -/
theorem theorem_9_6 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n) (EQ : Finset (Fin n × Fin n)) (VQ : Finset (Fin n)),
        2 ≤ n → 1 ≤ k → 1 ≤ f → 1 ≤ W → G.CostsBoundedOn EQ W →
        ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), k, f, W] EQ VQ
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let ms : ℝ := (EQ.card : ℝ) + k * VQ.card
          let Qs : Set (Fin n × Finset (Fin n × Fin n)) := {q | q.1 ∈ VQ ∧ q.2 ⊆ EQ ∧ q.2.card ≤ f}
          let enc : Fin n × Finset (Fin n × Fin n) → List ℤ := fun q => [((q.1 : ℕ) : ℤ)] ++ pairWords q.2
          let H : Finset (Fin n × Fin n) → CostMultigraph (Fin n) := fun U => G.plus (G.toggle U)
          let feas : Fin n × Finset (Fin n × Fin n) → Prop :=
            fun q => HasKDisjoint (H q.2) (IsArborescence (H q.2) q.1) k
          let minC : Fin n × Finset (Fin n × Fin n) → WithTop ℤ :=
            fun q => minKDisjointCost (H q.2) (IsArborescence (H q.2) q.1) k
          let fk : ℝ := ((f : ℝ) + k) ^ (ω + τ)
          let lgS : ℝ := Real.logb 2 ((W + k + n + EQ.card + k * VQ.card : ℕ) + 2 : ℝ)
          -- Decision
          O₁.Serves w inp ⌊C * (ms ^ 2 * kn ^ (ω - 2 + τ) + kn ^ (ω + τ))⌋₊ (C * ms ^ 2 * w) Qs enc
            ⌊C * fk⌋₊ (fun q mQ => Answers (feas q) (minC q) false mQ) err ∧
          -- Weighted
          O₂.Serves w inp ⌊C * (W * ms ^ 2 * kn ^ (ω - 1 + τ) + W * kn ^ 3) * lgS ^ K⌋₊
            (C * W * kn * ms ^ 2 * lgS ^ K) Qs enc
            ⌊C * W * kn * fk * Real.logb 2 ((W + k + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun q mQ => Answers (feas q) (minC q) true mQ) err := by sorry

end MatroidSensOracle.Supplement
