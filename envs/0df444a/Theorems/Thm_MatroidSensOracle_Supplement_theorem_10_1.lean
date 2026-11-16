-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_10_1
-- name    : MatroidSensOracle.Supplement.theorem_10_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:26:48.342531+00:00
-- url     : https://prove2.me/theorems/bbd2097b-50f4-4cb1-bf56-e11928d56c19
-- title:
--   Theorem 10.1 (space lower bound $\Omega(\min\{(m^\star)^2,n^2\})$ for flow and cut oracles under $f=2$)
-- statement:
--   For every error level $\delta\in[0,1/2)$ there are constants $c>0$ and $C$ such that for all positive integers $n,m^\star$ with $4\le m^\star\le n(n-1)$ the following holds. There are two distinct vertices $s,t$ of $V=\{0,\dots,n-1\}$, a set $E_Q$ of at most $Cm^\star$ pairs, and a class $\mathcal G$ of directed unit-capacity graphs on $V$, each with edge set disjoint from $E_Q$, such that for each of the five problems
--
--   1. the 1-bounded $(s,t)$-maximum flow $\min(1,\lambda_{G+U}(s,t))$,
--   2. the $(s,t)$-minimum cut value,
--   3. the global directed minimum cut value $\mu_{G+U}$,
--   4. the $s$-min-cut value $\mu_{G+U}(s)$,
--   5. the existence of an $s$-rooted spanning arborescence,
--
--   every subset sensitivity oracle that answers every query $U\subseteq E_Q$ with $|U|\le2$ on every $G\in\mathcal G$ correctly with probability at least $1-\delta$ stores at least
--   $$c\cdot\min\{(m^\star)^2,n^2\}$$
--   bits on some member of $\mathcal G$, irrespective of its query time.
--
--   Together with Theorems 5.2 and 5.5 this shows that the space of those oracles is nearly optimal for a constant number of updates.
--
--   **Formalization Note** The oracle is information-theoretic: its preprocessing maps a graph and random coins to a bit string, its query maps the string, the query and fresh coins to an answer; both are arbitrary measurable maps.
--
--   Differences from the source:
--   - reading: there exists a graph G (and E_Q) such that any oracle requires Ω(·) bits → there is a class 𝒢 of graphs sharing V, the designated vertices and E_Q such that every oracle correct on all of 𝒢 stores at least c·min((m★)², n²) bits on some member; reason: for a single fixed graph an oracle needs no space; the proof's family indexed by a p × p matrix is what the theorem asserts
--   - generalization: subset sensitivity oracles (deterministic answers in the proof's counting argument) → information-theoretic randomized oracles (arbitrary measurable maps, no time bound) erring with probability at most δ per query, for every δ ∈ [0, 1/2), c depending on δ; reason: δ = 0 is the deterministic case of the proof; the paper's oracles are Monte Carlo
--   - encoding: f = 2 updates → queries U ⊆ E_Q with |U| ≤ 2; reason: the oracle supports at most two updates
--   - reading: (s, t) minimum cut (problem (a)) → the (s, t)-min-cut value; reason: the proof of (a): 'equivalently, the (s, t)-minimum cut value'
--   - reading: |E_Q| = O(m★) → |E_Q| ≤ C·m★ with C depending on δ only; reason: O(·) with a constant independent of n and m★
--   - encoding: Ω(min{(m★)², n²}) bits → at least c·min((m★)², n²) bits on some member for some coin sequence (worst-case space); reason: c > 0 independent of n and m★
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 10.1, pp.54–55 (PDF pp.57–58)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

open Classical in
/-- **Theorem 10.1 (space lower bound: flows and cuts).** Choudhary, Kumar, Saggi, arXiv:2609.01283
(held version, sha256 0de50841…), pp.54–55 (PDF pp.57–58): "For any positive integers n and m★
satisfying 4 ⩽ m★ ⩽ n(n−1), there exists an n-vertex directed unit-capacity graph G = (V, E) and a
susceptible edge set E_Q disjoint from E, with |E_Q| = O(m★), such that any subset sensitivity oracle
supporting at most f = 2 updates requires Ω(min{(m★)², n²}) bits of space for each of the following
problems:
(a) k-bounded (s, t) maximum flow and (s, t) minimum cut, for k = 1;
(b) Global directed minimum cut;
(c) s-min-cut and s-rooted spanning arborescences (fixed source s)."
p.54: "any (s, t)-Bounded Max-Flow sensitivity oracle requires Ω(min{(m★)², n²}) space, irrespective of
the query time".

**Formalization Note.**
* A space lower bound for one fixed graph is empty (an oracle built for that graph alone stores
  nothing), so "a graph G" is read as the family the proof (p.55) uses: a class `𝒢` of graphs on
  `V = Fin n` sharing `s ≠ t` and `E_Q`, with `E_Q ∩ E = ∅` for every member and `|E_Q| ≤ C m★`.
  Every oracle that is correct on all of `𝒢` stores at least `c min((m★)², n²)` bits on some member.
* Oracle model (`InfoOracle`): arbitrary maps, no time bound ("irrespective of the query time"); the
  preprocessing sends a graph and coins to a bit string, the query sends the string, a query
  `U ⊆ E_Q` with `|U| ≤ 2` (toggles, here insertions) and fresh coins to an answer. Correct with
  error `δ`: every member and query is answered wrongly with probability at most `δ`. The bound holds
  for every `δ ∈ [0, 1/2)`, with `c` depending on `δ` only; `δ = 0` is the deterministic case.
* The five answers: (a) `min(1, λ_{G+U}(s, t))` and the `(s, t)`-min-cut value (least capacity of a
  vertex set `A ∋ s`, `t ∉ A`); (b) `μ_{G+U}`; (c) `μ_{G+U}(s)` and whether `G + U` has an `s`-rooted
  spanning arborescence. -/
theorem theorem_10_1 :
    ∀ δ : ℝ, 0 ≤ δ → δ < 1 / 2 → ∃ c C : ℝ, 0 < c ∧
      ∀ n ms : ℕ, 4 ≤ ms → ms ≤ n * (n - 1) →
        ∃ (s t : Fin n) (EQ : Finset (Fin n × Fin n)) (𝒢 : Set (InputGraph n)),
          s ≠ t ∧ (EQ.card : ℝ) ≤ C * ms ∧ (∀ G ∈ 𝒢, Disjoint G.E EQ) ∧
          let Qs : Set (Finset (Fin n × Fin n)) := {U | U ⊆ EQ ∧ U.card ≤ 2}
          let H : InputGraph n → Finset (Fin n × Fin n) → CostMultigraph (Fin n) :=
            fun G U => G.plus (G.toggle U)
          let B : ℝ := c * min ((ms : ℝ) ^ 2) ((n : ℝ) ^ 2)
          -- (a) 1-bounded (s, t) max-flow
          (∀ O : InfoOracle (InputGraph n) (Finset (Fin n × Fin n)) ℕ,
            O.Correct 𝒢 Qs (fun G U => min 1 ((H G U).maxFlow s t)) δ → O.SpaceAtLeast 𝒢 B) ∧
          -- (a) (s, t) min-cut value
          (∀ O : InfoOracle (InputGraph n) (Finset (Fin n × Fin n)) ℕ,
            O.Correct 𝒢 Qs (fun G U => sInf {k : ℕ | ∃ A : Finset (Fin n), s ∈ A ∧ t ∉ A ∧
              (H G U).cutCapacity A = k}) δ → O.SpaceAtLeast 𝒢 B) ∧
          -- (b) global directed min-cut value
          (∀ O : InfoOracle (InputGraph n) (Finset (Fin n × Fin n)) ℕ,
            O.Correct 𝒢 Qs (fun G U => globalMinCutValue (H G U)) δ → O.SpaceAtLeast 𝒢 B) ∧
          -- (c) s-min-cut value
          (∀ O : InfoOracle (InputGraph n) (Finset (Fin n × Fin n)) ℕ,
            O.Correct 𝒢 Qs (fun G U => sMinCutValue (H G U) s) δ → O.SpaceAtLeast 𝒢 B) ∧
          -- (c) existence of an s-rooted spanning arborescence
          (∀ O : InfoOracle (InputGraph n) (Finset (Fin n × Fin n)) Bool,
            O.Correct 𝒢 Qs (fun G U => decide (∃ X, IsArborescence (H G U) s X)) δ →
              O.SpaceAtLeast 𝒢 B) := by sorry

end MatroidSensOracle.Supplement
