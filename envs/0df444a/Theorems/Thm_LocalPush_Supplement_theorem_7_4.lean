-- Prove2me | Theorems.Thm_LocalPush_Supplement_theorem_7_4
-- name    : LocalPush.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:22:43.000209+00:00
-- url     : https://prove2.me/theorems/e7da570b-1522-41ae-8cef-13ad5bf67a81
-- title:
--   Theorem 7.4 — query lower bound $\Omega(\min\{m,\gamma^{-1}\epsilon^{-2/3},\gamma^{-3}\epsilon^{-2}/\min\{d(s),d(t)\}^2\})$ for single-pair effective resistance
-- statement:
--   There are universal constants $c>0$ and $c_1,C_1>0$ such that the following holds. Let $n\ge100$ and $n\le m\le n^2$ be integers, $1\le d_s,d_t\le n$ integers, $0<\gamma\le1/4000$ and
--   $$0<\epsilon\le\min\Big\{\frac1{100},\ \frac{\gamma^{-1}}{400\min\{d_s,d_t\}}\Big\}.$$
--   Then there is a finite nonempty family of inputs, each consisting of a connected simple undirected graph $G$ on $N$ nodes with $|E|$ edges, given by adjacency lists, with spectral gap $\nu_2(G)\ge\gamma$, and two distinct nodes $s,t$ with $d(s)=d_s$, $d(t)=d_t$, where $c_1n\le N\le C_1n$ and $c_1m\le|E|\le C_1m$, such that every randomized adaptive query algorithm (with degree, indexed-neighbour and adjacency queries and uniform node samples, and unrestricted internal computation) that, on every input of the family, outputs with probability at least $2/3$ an estimate within $\epsilon$ of the effective resistance $R(s,t)$ makes, on some input of the family, at least
--   $$c\cdot\min\Big\{m,\ \gamma^{-1}\epsilon^{-2/3},\ \frac{\gamma^{-3}\epsilon^{-2}}{\min\{d_s,d_t\}^2}\Big\}\tag{45}$$
--   queries in expectation.
--
--   Together with Theorem 6.3 this determines the query complexity of single-pair effective resistance estimation on expanders up to logarithmic factors. The accuracy restriction is necessary: by the bound $R(s,t)\le(1/d(s)+1/d(t))/\gamma$, larger $\epsilon$ admits a trivial estimate.
--
--   **Formalization Note** The algorithm is quantified after the family. $R$ and $\nu_2$ are the definitions of Theorem 6.3.
--
--   Differences from the source:
--   - reading: Ω(·), Θ(n) nodes, Θ(m) edges → constants c > 0 and c₁, C₁ > 0 chosen before n, m, d(s), d(t), γ, ϵ; c₁n ≤ |V| ≤ C₁n and c₁m ≤ |E| ≤ C₁m for every graph of the family; reason: the usual meaning of asymptotic notation for a family statement, uniform in all parameters
--   - reading: "there is a family … for which estimating R(s, t) … with success probability at least 2/3 on every input requires … expected queries in the worst case" → ∃ finite nonempty family, ∀ measurable randomized adaptive query algorithm succeeding with probability ≥ 2/3 on every input of the family, ∃ input with expected query count ≥ c·min{…}; reason: the family is fixed before the algorithm, which may therefore know the parameters and the family
--   - encoding: randomized algorithm with degree, indexed-neighbor queries, adjacency tests, uniform node samples, unrestricted internal computation → QueryAlg: an arbitrary function of a fair-coin tape, s, t and the history, measurable in the tape; uniform samples from an independent tape; cost = expected number of queries before halting, ∞ if it fails to halt with positive probability; reason: every distribution over deterministic strategies is the image of fair coins under a measurable map
--   - encoding: ν₂(G) ≥ γ; R(s, t) with L⁺ → γ ≤ nu2 G (variational form of p.15); effRes via the published Moore–Penrose pseudoinverse; reason: the same definitions as Theorem 6.3; p.15 states the variational form equals the eigenvalue
--   - encoding: connected, undirected, unweighted simple graphs → adjacency lists satisfying IsAdjList (simple, symmetric, no isolated nodes) whose graph is Connected; reason: a connected graph with at least two nodes has no isolated nodes
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §7.2, Theorem 7.4, p.42 (PDF p.42); R(s, t) and ν₂, §4, p.15

import Mathlib
import Definitions.Def_LocalPush_Layout
import Definitions.Def_LocalPush_Supplement_Spectral
import Definitions.Def_LocalPush_Supplement_QueryAlg

open Finset Matrix

namespace LocalPush

namespace Supplement

/-- **Theorem 7.4 (query lower bound for single-pair effective resistance).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §7.2, Theorem 7.4, p.42
(PDF p.42); `R(s, t)` and `ν₂` are defined on p.15.

"For every choice of integers n ≥ 100 and n ≤ m ≤ n², prescribed degrees 1 ≤ d(s), d(t) ≤ n, spectral-gap
lower bound 0 < γ ≤ 1/4000, and accuracy 0 < ϵ ≤ min{1/100, γ^{−1}/(400 min{d(s), d(t)})}, there is a family
of connected, undirected, unweighted simple graphs G with Θ(n) nodes, Θ(m) edges, spectral gap ν2(G) ≥ γ, and
distinct nodes s, t of degrees d(s), d(t), respectively, for which estimating R(s, t) to additive error ϵ with
success probability at least 2/3 on every input requires Ω(min{m, γ^{−1}ϵ^{−2/3},
γ^{−3}ϵ^{−2}/min{d(s), d(t)}²}) (45) expected queries in the worst case. The algorithm may use degree queries,
indexed-neighbor queries, adjacency tests, and uniform node samples, with unrestricted internal computation."

There are universal constants `c > 0` (the `Ω`) and `0 < c₁, C₁` (the `Θ`) such that for all integers
`n ≥ 100`, `n ≤ m ≤ n²`, `1 ≤ d_s, d_t ≤ n` and reals `0 < γ ≤ 1/4000`,
`0 < ϵ ≤ min{1/100, γ⁻¹/(400 min{d_s, d_t})}` there is a finite nonempty family of inputs, each a connected
simple graph given by adjacency lists (any order), with `c₁n ≤ |V| ≤ C₁n`, `c₁m ≤ |E| ≤ C₁m`, `ν₂(G) ≥ γ`
and distinct marked nodes `s, t` of degrees `d_s, d_t`, such that every randomized adaptive query algorithm
(`QueryAlg`) that outputs a value within `ϵ` of `R(s, t)` with probability at least `2/3` on every input of
the family has expected query count at least `c·min{m, γ⁻¹ϵ^{−2/3}, γ⁻³ϵ⁻²/min{d_s, d_t}²}` on some input.

**Formalization Note.**
* The algorithm is quantified after the family, so it may depend on all parameters and on the family.
* `ν₂` is the variational form of p.15 and `R` uses the Moore–Penrose pseudoinverse of `L = D − A`
  (`Spectral`), the same definitions as in Theorem 6.3.
* The expected query count is `∞` for an algorithm that fails to halt with positive probability. -/
theorem theorem_7_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      ∀ (n m ds dt : ℕ) (γ ϵ : ℝ), 100 ≤ n → n ≤ m → m ≤ n ^ 2 → 1 ≤ ds → ds ≤ n → 1 ≤ dt → dt ≤ n →
        0 < γ → γ ≤ 1 / 4000 → 0 < ϵ → ϵ ≤ min (1 / 100) (γ⁻¹ / (400 * (min ds dt : ℕ))) →
        ∃ fam : Set QInput, fam.Finite ∧ fam.Nonempty ∧
          (∀ I ∈ fam, IsAdjList I.nbrs ∧ (toGraph I.nbrs).Connected ∧ I.s ≠ I.t ∧
            (I.nbrs I.s).length = ds ∧ (I.nbrs I.t).length = dt ∧
            c₁ * n ≤ (I.N : ℝ) ∧ (I.N : ℝ) ≤ C₁ * n ∧
            c₁ * m ≤ (numEdges (toGraph I.nbrs) : ℝ) ∧ (numEdges (toGraph I.nbrs) : ℝ) ≤ C₁ * m ∧
            γ ≤ nu2 (toGraph I.nbrs)) ∧
          ∀ A : QueryAlg, A.IsMeasurable →
            (∀ I ∈ fam, Succeeds A I fun y => |y - effRes (toGraph I.nbrs) I.s I.t| ≤ ϵ) →
            ∃ I ∈ fam, ENNReal.ofReal (c * min (m : ℝ)
              (min (γ⁻¹ * ϵ ^ (-(2 / 3 : ℝ)))
                (γ⁻¹ ^ 3 * ϵ⁻¹ ^ 2 / ((min ds dt : ℕ) : ℝ) ^ 2))) ≤ qcost A I := by sorry

end Supplement

end LocalPush
