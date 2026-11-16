-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_10_3
-- name    : MatroidSensOracle.Supplement.theorem_10_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:27:39.9988+00:00
-- url     : https://prove2.me/theorems/f3ca5f4f-5307-4f5f-8c24-49acc36284c6
-- title:
--   Theorem 10.3 (space lower bound $\Omega(\min((m^\star)^2,n^2))$ for bipartite matching oracles under $f=2$)
-- statement:
--   For every error level $\delta\in[0,1/2)$ there are constants $c,c_1>0$ and $C$ such that for all positive integers $n,m^\star$ with $4\le m^\star\le n(n-1)$ the following holds. There are a vertex set $L\subseteq V=\{0,\dots,n-1\}$, a set $E_Q$ of pairs with $c_1m^\star\le|E_Q|\le Cm^\star$, and a class $\mathcal G$ of undirected graphs on $V$, each bipartite with sides $L$ and $V\setminus L$ and each containing $E_Q$, such that every subset sensitivity oracle that reports the maximum matching size of $G+U$ for every member $G$ and every $U\subseteq E_Q$ with $|U|\le 2$, correctly with probability at least $1-\delta$, stores at least
--   $$c\cdot\min\{(m^\star)^2,n^2\}$$
--   bits on some member of $\mathcal G$, irrespective of its query time.
--
--   Differences from the source:
--   - reading: there exists a graph G (and E_Q) such that any oracle requires Ω(·) bits → there is a class 𝒢 of graphs sharing V, the designated vertices and E_Q such that every oracle correct on all of 𝒢 stores at least c·min((m★)², n²) bits on some member; reason: for a single fixed graph an oracle needs no space; the proof's family indexed by a p × p matrix is what the theorem asserts
--   - generalization: subset sensitivity oracles (deterministic answers in the proof's counting argument) → information-theoretic randomized oracles (arbitrary measurable maps, no time bound) erring with probability at most δ per query, for every δ ∈ [0, 1/2), c depending on δ; reason: δ = 0 is the deterministic case of the proof; the paper's oracles are Monte Carlo
--   - encoding: f = 2 updates → queries U ⊆ E_Q with |U| ≤ 2; reason: the oracle supports at most two updates
--   - reading: |E_Q| = Θ(m★) → c₁·m★ ≤ |E_Q| ≤ C·m★; reason: Θ with constants independent of n and m★
--   - encoding: an n-vertex bipartite graph G = (L ∪ R, E) → undirected graphs on Fin n (edges (a, b), a < b) whose every edge joins L and its complement; reason: a bipartition of the vertex set
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 10.3, p.57 (PDF p.60)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 10.3 (space lower bound: bipartite matching).** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.57 (PDF p.60): "Let n, m★ be positive integers
with 4 ⩽ m★ ⩽ n(n−1). There exists an n-vertex bipartite graph G = (L ∪ R, E) and a susceptible set
E_Q ⊆ E of size Θ(m★) such that any subset sensitivity oracle for maximum bipartite matching requires
Ω(min((m★)², n²)) bits of space under f = 2 updates." p.57: "any oracle which reports the maximum
matching size of a bipartite graph, after f = 2 edge updates, requires at least Ω(min((m★)², n²))
space, irrespective of the query time."

**Formalization Note.**
* As in `theorem_10_1`, "a graph" is read as the family of the proof (p.57): a class `𝒢` of undirected
  graphs on `Fin n` (edges `(a, b)`, `a < b`), all bipartite with the same side `L` (every edge joins
  `L` and its complement), with one susceptible set `E_Q ⊆ E` of every member, `c₁ m★ ≤ |E_Q| ≤ C m★`.
* Queries: `U ⊆ E_Q`, `|U| ≤ 2` (toggles; since `E_Q ⊆ E`, deletions). The answer is the maximum size
  of a matching of `G + U`.
* Oracle model, error `δ ∈ [0, 1/2)` and space as in `theorem_10_1`. -/
theorem theorem_10_3 :
    ∀ δ : ℝ, 0 ≤ δ → δ < 1 / 2 → ∃ c c₁ C : ℝ, 0 < c ∧ 0 < c₁ ∧
      ∀ n ms : ℕ, 4 ≤ ms → ms ≤ n * (n - 1) →
        ∃ (L : Finset (Fin n)) (EQ : Finset (Fin n × Fin n)) (𝒢 : Set (InputGraph n)),
          c₁ * ms ≤ (EQ.card : ℝ) ∧ (EQ.card : ℝ) ≤ C * ms ∧
          (∀ G ∈ 𝒢, G.Undirected ∧ EQ ⊆ G.E ∧ ∀ e ∈ G.E, (e.1 ∈ L ↔ e.2 ∉ L)) ∧
          ∀ O : InfoOracle (InputGraph n) (Finset (Fin n × Fin n)) ℕ,
            O.Correct 𝒢 {U | U ⊆ EQ ∧ U.card ≤ 2} (fun G U => maxMatching (G.plus (G.toggle U))) δ →
              O.SpaceAtLeast 𝒢 (c * min ((ms : ℝ) ^ 2) ((n : ℝ) ^ 2)) := by sorry

end MatroidSensOracle.Supplement
