-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_9_1
-- name    : MatroidSensOracle.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:19:52.660199+00:00
-- url     : https://prove2.me/theorems/840d5742-1b67-4b99-8986-0f05b556a56b
-- title:
--   Theorem 9.1 (subset all-pairs $k$-bounded flow, nearest min-cut and min-cost flow oracles; corrected: Bounded Flow and Min-Cost preprocessing include $(kn)^\omega$ and $W(kn)^3$)
-- statement:
--   Let $G=(V,E,c)$ be an $n$-vertex directed graph with integer edge costs in $[-W,W]$, let $V_Q\subseteq V$ be a set of query vertices, $E_Q$ a set of susceptible pairs (possibly not in $E$), and $1\le k\le n$. Let $m^\star=|E_Q|+k|V_Q|$. A query is $(s,t,U)$ with $s,t\in V_Q$, $s\ne t$, $U\subseteq E_Q$, $|U|\le f$; it toggles the pairs of $U$ (deletes those in $E$, inserts the others). Let $\lambda^*=\min(k,\lambda_{G+U}(s,t))$.
--
--   For every $c>0$ and $\tau>0$ there are constants $C,K,b$ and three oracles on the randomized word RAM answering every fixed query wrongly with probability at most $n^{-c}$:
--
--   1. **Bounded flow:** preprocessing $C\bigl((kn)^{\omega-2+\tau}(m^\star)^2+(kn)^{\omega+\tau}\bigr)$, space $C(m^\star)^2$ words, query $C(f+k)^{\omega+\tau}\log_2(k+1)$; output $\lambda^*$.
--   2. **Nearest min-cut:** preprocessing $C(kn)^{\omega-2+\tau}(m^\star+n|V_Q|)^2$, space $C(m^\star+n|V_Q|)^2$ words, query $C(f+k)^{\omega+\tau}n$; output $\mathrm{NMC}_{G+U}(s,t)$ whenever $\lambda^*<k$.
--   3. **Min-cost flow:** preprocessing $\tilde O(W(kn)^{\omega-1}(m^\star)^2+W(kn)^3)$, space $\tilde O(Wkn(m^\star)^2)$ bits, query $\tilde O(Wkn(f+k)^{\omega})$; output the least cost of an $(s,t)$-flow of value $\lambda^*$.
--
--   With $k=1$ these give subset reachability and distance sensitivity oracles (Corollary 9.2).
--
--   **Correction.** As printed, rows 1 and 3 allow preprocessing smaller than the input: with $k=1$, $V_Q=\{s,t\}$, $E_Q=\emptyset$ ($m^\star=2$) and a graph with $\Theta(n)$ edges, row 1 allows $O(n^{\omega-2+\tau})=o(n)$ steps, so the preprocessing cannot read every edge, while $\lambda^*$ depends on every edge and the query sees only the stored string. The added terms are those the paper prints for the same instantiation of Theorem 3.5 with the same $m^\star$ (Theorems 9.6, 9.8, 9.12; Theorem 5.2 for $W(kn)^3$). Row 2 is as printed.
--
--   Differences from the source:
--   - correction: Bounded Flow preprocessing O((kn)^{ω−2}(m★)²); Min-Cost Flow preprocessing Õ(W(kn)^{ω−1}(m★)²) → C·((kn)^{ω−2+τ}(m★)² + (kn)^{ω+τ}) and C·W·((kn)^{ω−1+τ}(m★)² + (kn)³)·(log₂(Z+2))^K; reason: counterexample: k = 1, V_Q = {s, t}, E_Q = ∅ (m★ = 2), G with Θ(n) edges: the printed bound o(n) steps cannot read every edge, yet λ∗ = min(1, λ_G(s, t)) and the min-cost value depend on every edge and Q sees only the stored string; the added terms are those of the same Theorem 3.5 instantiation in Theorems 9.6/9.8/9.12
--   - reading: sensitivity oracles with preprocessing time, space and query time (machine unstated) → programs (P, Q) on the base randomized word RAM; Q reads only the stored bit string and the query; times are worst case over all coins; the programs work for every word width w ≥ b(⌊log₂(Z+2)⌋+1); reason: the machine of the published goal Theorem 5.5 (base mission); the paper's bounds are word-RAM bounds
--   - reading: with high probability → for every c > 0 (constants and programs may depend on c), each fixed query is answered wrongly with probability at most n^{−c}; reason: the standard meaning, as in the published goal Theorem 5.5
--   - encoding: O(x^ω), O(x^{ω−1}), O(x^{ω−2}) → C·x^{ω+τ}, C·x^{ω−1+τ}, C·x^{ω−2+τ} for every τ > 0, with ω = omega ℂ; reason: ω is an infimum that need not be attained; base convention
--   - reading: Õ(X) → C·X·(log₂(Z+2))^K, Z the sum of the parameters occurring in X; reason: Õ hides polylogarithmic factors in the parameters of the bound
--   - reading: space bounds printed without a log n factor → C·X·w bits, i.e. X machine words of w bits; reason: the paper's own convention: the abstract's O((fn)²) space is Theorem 5.5's O((fn)² log n) bits; bounds with log n or Õ count bits
--   - generalization: a susceptible set E_Q ⊆ E; updates U ⊆ E_Q consisting of insertions and deletions → E_Q any set of pairs (with costs), possibly not in E; a query U ⊆ E_Q, |U| ≤ f, deletes U ∩ E and inserts U ∖ E; reason: §9.1: E_Q 'may include edges not currently in E'; the printed E_Q ⊆ E is the special case
--   - encoding: log k → log₂(k + 1); reason: so that k = 1 does not zero the bound
--   - encoding: (s, t) ∈ V_Q² → s ≠ t; reason: (s, t)-cuts are defined only for s ≠ t
--   - encoding: G + U → the multigraph of the surviving edges followed by the inserted edges; an inserted edge is a new edge, possibly parallel; reason: base convention (InputGraph.plus); no instance of the source is excluded
--   - encoding: an n-vertex graph and the parameters of the bounds → n ≥ 2, 1 ≤ k ≤ n, f ≥ 1, W ≥ 1, |V_Q| ≥ 1, costs on E ∪ E_Q in [−W, W]; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined; V_Q = ∅ admits no query and would make the printed bounds 0
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 9.1, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 9.1 (subset all-pairs `k`-bounded flow; corrected: preprocessing of the Bounded Flow and
Min-Cost Flow rows includes the `(kn)^ω` and `W(kn)³` terms).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), p.45 (PDF p.48): "Let G = (V, E, c) be an n-vertex directed graph
with integer edge costs in [−W, W] with designated sets V_Q ⊆ V and E_Q ⊆ E, and let k ∈ [1, n]. Let
m★ := |E_Q| + k|V_Q|. Then there exist the following subset sensitivity oracles that, for any query
(s, t, U) ∈ V_Q² × E_Q^f, answer queries on G + U with high probability:"

| Oracle | Prep. | Space | Query | Output |
|---|---|---|---|---|
| Bounded Flow | O((kn)^{ω−2}(m★)²) | O((m★)²) | O((f + k)^ω log k) | λ∗ = min(k, λ_{G+U}(s, t)) |
| Nearest Min-Cut | O((kn)^{ω−2}(m★ + n|V_Q|)²) | O((m★ + n|V_Q|)²) | O((f + k)^ω n) | NMC_{G+U}(s, t) (if λ∗ < k) |
| Min-Cost Flow | Õ(W(kn)^{ω−1}(m★)²) | Õ(Wkn(m★)²) | Õ(Wkn(f + k)^ω) | Min-cost for flow of value λ∗ |

§9.1.1, p.45: "a set of susceptible edges E_Q (which may include edges not currently in E) subject to
insertions or deletions. Any query (s, t, U) satisfies s, t ∈ V_Q and U ⊆ E_Q with |U| ⩽ f."

**Formalization Note.**
* Subset model: `E_Q` is any set of pairs (each with its cost `G.cost e`), possibly not in `E`; a
  query `U ⊆ E_Q`, `|U| ≤ f`, deletes `U ∩ E` and inserts `U ∖ E` (`G.toggle U`). The case
  `E_Q ⊆ E` printed in the theorem is a special case.
* Machine and oracle semantics: the base randomized word RAM; `P` reads
  `encodeSubset G [n, k, f, W] E_Q V_Q`, `Q` reads only the stored string and
  `[s, t] ++ pairWords U`. `ω = omega ℂ`; `O(x^{ω−2})`, `O(x^{ω−1})`, `O(x^ω)` are
  `C x^{ω−2+τ}`, `C x^{ω−1+τ}`, `C x^{ω+τ}` for every `τ > 0`; `log k = log₂(k + 1)`;
  `Õ(X) = C X (log₂(Z + 2))^K`, `Z` the sum of the parameters in `X`.
* Space: `O((m★)²)` and `O((m★ + n|V_Q|)²)` count words (`· w` bits); the `Õ` bound counts bits.
* With high probability: for every `c > 0` each fixed query errs with probability at most `n^{−c}`.
* Instances: `n ≥ 2`, `1 ≤ k ≤ n`, `f ≥ 1`, `W ≥ 1`, costs on `E ∪ E_Q` in `[−W, W]`; `s ≠ t`.
* Outputs as in `theorem_5_2`.
* **Correction (moderation).** As printed, the Bounded Flow preprocessing `O((kn)^{ω−2}(m★)²)` and the
  Min-Cost preprocessing `Õ(W(kn)^{ω−1}(m★)²)` can be smaller than the input: with `k = 1`,
  `V_Q = {s, t}`, `E_Q = ∅` (so `m★ = 2`) and `G` having `Θ(n)` edges, the first bound is
  `O(n^{ω−2+τ}) = o(n)` for small `τ`, so `P` cannot read every edge, while `λ∗ = min(1, λ_G(s, t))`
  (and the min-cost value) depends on every edge and `Q` sees only the stored string; an oracle
  erring with probability `≤ n^{−c}` cannot exist. The rows are corrected by the term the paper
  prints for the same Theorem 3.5 instantiation with the same `m★ = |E_Q| + k|V_Q|` (Theorems 9.6,
  9.8, 9.12): `+ (kn)^ω` (Bounded Flow) and `+ W(kn)³` (Min-Cost Flow, as in Theorem 5.2). The Nearest
  Min-Cut row is kept as printed (its bound is at least `n²` once `V_Q ≠ ∅`).
* `V_Q ≠ ∅`: with `V_Q = E_Q = ∅` there is no query and the printed bounds are `0`, which no run
  meets (a run takes at least one step); this excludes only that degenerate instance. -/
theorem theorem_9_1 :
    ∀ c : ℝ, 0 < c → ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (K b : ℕ) (O₁ O₂ O₃ : Oracle),
      ∀ (n k f W : ℕ) (G : InputGraph n) (EQ : Finset (Fin n × Fin n)) (VQ : Finset (Fin n)),
        2 ≤ n → 1 ≤ k → k ≤ n → 1 ≤ f → 1 ≤ W → 1 ≤ VQ.card → G.CostsBoundedOn EQ W →
        ∀ w : ℕ, b * (Nat.log 2 (n + k + f + W + 2) + 1) ≤ w →
          let ω := OAI.MatrixMultiplication.Arithmetic.omega ℂ
          let inp := encodeSubset G [(n : ℤ), k, f, W] EQ VQ
          let err : ℝ := (n : ℝ) ^ (-c)
          let kn : ℝ := (k : ℝ) * n
          let ms : ℝ := (EQ.card : ℝ) + k * VQ.card
          let mc : ℝ := ms + n * VQ.card
          let Qs : Set (Fin n × Fin n × Finset (Fin n × Fin n)) :=
            {q | q.1 ∈ VQ ∧ q.2.1 ∈ VQ ∧ q.1 ≠ q.2.1 ∧ q.2.2 ⊆ EQ ∧ q.2.2.card ≤ f}
          let enc : Fin n × Fin n × Finset (Fin n × Fin n) → List ℤ :=
            fun q => [((q.1 : ℕ) : ℤ), ((q.2.1 : ℕ) : ℤ)] ++ pairWords q.2.2
          let lam : Fin n × Fin n × Finset (Fin n × Fin n) → ℕ :=
            fun q => min k ((G.plus (G.toggle q.2.2)).maxFlow q.1 q.2.1)
          let fk : ℝ := ((f : ℝ) + k) ^ (ω + τ)
          -- Bounded Flow
          O₁.Serves w inp ⌊C * (kn ^ (ω - 2 + τ) * ms ^ 2 + kn ^ (ω + τ))⌋₊ (C * ms ^ 2 * w) Qs enc
            ⌊C * fk * Real.logb 2 ((k : ℝ) + 1)⌋₊
            (fun q mQ => (mQ 0).toNat = lam q) err ∧
          -- Nearest Min-Cut (if λ∗ < k)
          O₂.Serves w inp ⌊C * kn ^ (ω - 2 + τ) * mc ^ 2⌋₊ (C * mc ^ 2 * w) Qs enc
            ⌊C * fk * n⌋₊
            (fun q mQ => lam q < k →
              (G.plus (G.toggle q.2.2)).IsNearestMinCut q.1 q.2.1 (outSet mQ)) err ∧
          -- Min-Cost Flow of value λ∗
          O₃.Serves w inp
            ⌊C * W * (kn ^ (ω - 1 + τ) * ms ^ 2 + kn ^ 3) *
              Real.logb 2 ((W + k + n + EQ.card + k * VQ.card : ℕ) + 2 : ℝ) ^ K⌋₊
            (C * W * kn * ms ^ 2 * Real.logb 2 ((W + k + n + EQ.card + k * VQ.card : ℕ) + 2 : ℝ) ^ K)
            Qs enc
            ⌊C * W * kn * fk * Real.logb 2 ((W + k + n + f : ℕ) + 2 : ℝ) ^ K⌋₊
            (fun q mQ => ((mQ 0).toInt : WithTop ℤ) =
              (G.plus (G.toggle q.2.2)).minCostFlow q.1 q.2.1 (lam q)) err := by sorry

end MatroidSensOracle.Supplement
