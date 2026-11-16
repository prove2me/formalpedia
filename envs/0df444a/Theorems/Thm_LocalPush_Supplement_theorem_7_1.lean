-- Prove2me | Theorems.Thm_LocalPush_Supplement_theorem_7_1
-- name    : LocalPush.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:21:55.931227+00:00
-- url     : https://prove2.me/theorems/51409617-0bc5-4306-a270-9da36d44e55d
-- title:
--   Theorem 7.1 — query lower bound $\Omega(\min\{m,\alpha^{-1/2}\sqrt{d(t)/\theta},\min\{1,d(t)/d(s)\}/(\alpha\theta),d(t)/\theta\})$ for single-pair PageRank
-- statement:
--   There are universal constants $c>0$ and $c_1,C_1>0$ such that the following holds. Let $n\le m\le n^2$ be integers, $1\le d_s,d_t\le n$ integers, $0<\alpha\le1/2$ and $0<\theta\le\min\{1,d_t/d_s\}$. Then there is a finite nonempty family of inputs, each consisting of a simple undirected graph without isolated nodes on $N$ nodes with $|E|$ edges, given by adjacency lists sorted by degree, and two distinct nodes $s,t$ with $d(s)=d_s$, $d(t)=d_t$, where
--   $$c_1n\le N\le C_1n,\qquad c_1m\le|E|\le C_1m,$$
--   such that every randomized adaptive query algorithm (with degree, neighbour and adjacency queries and uniform node samples) that, on every input of the family, outputs with probability at least $2/3$ an estimate $\hat p$ with
--   $$|\hat p-\mathrm{pr}_\alpha(s,t)|\le10^{-9}\max\{\mathrm{pr}_\alpha(s,t),\theta\}$$
--   makes, on some input of the family, at least
--   $$c\cdot\min\Big\{m,\ \frac1{\alpha^{1/2}}\sqrt{\frac{d_t}\theta},\ \frac{\min\{1,d_t/d_s\}}{\alpha\theta},\ \frac{d_t}\theta\Big\}\tag{43}$$
--   queries in expectation.
--
--   The bound matches the query upper bound of Theorem 6.1 for constant $\epsilon$, so the query complexity of single-pair PageRank estimation is settled. The graphs may be disconnected, which the Remark on p.38 shows is necessary for arbitrarily small $\alpha$.
--
--   **Formalization Note** The algorithm is quantified after the family. Sorted access means each list is in nondecreasing order of degree.
--
--   Differences from the source:
--   - reading: Ω(·), Θ(n) nodes, Θ(m) edges → constants c > 0 and c₁, C₁ > 0 chosen before n, m, d(s), d(t), α, θ; c₁n ≤ |V| ≤ C₁n and c₁m ≤ |E| ≤ C₁m for every graph of the family; reason: the usual meaning of asymptotic notation for a family statement, uniform in all parameters
--   - reading: "there is a family … for which estimating … with success probability at least 2/3 on every input requires … expected queries in the worst case" → ∃ finite nonempty family, ∀ measurable randomized adaptive query algorithm succeeding with probability ≥ 2/3 on every input of the family, ∃ input of the family with expected query count ≥ c·min{…}; reason: the paper's family is fixed before the algorithm; an algorithm chosen after the family may know n, m, the parameters and the family, which covers "can be given the values of n and m"
--   - encoding: the algorithm can access the neighbor lists sorted by degree → every list of every graph of the family is in nondecreasing order of degree; reason: sortedness is a property of the input representation; with degree queries nonincreasing order is the same (index d(v) − 1 − i)
--   - encoding: randomized algorithm with degree, neighbor, adjacency queries and uniform node samples → QueryAlg: a function of a fair-coin tape, s, t and the history, measurable in the tape; uniform samples from an independent tape; cost = expected number of queries before halting, ∞ if it fails to halt with positive probability; reason: every distribution over deterministic strategies is the image of fair coins under a measurable map (the strategy space is standard Borel)
--   - encoding: unweighted, undirected simple graphs → adjacency lists satisfying IsAdjList (simple, symmetric, no isolated nodes); reason: no isolated nodes is the paper's standing assumption (p.4); the paper's construction has none
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §7.1, Theorem 7.1, p.38 (PDF p.38)

import Mathlib
import Definitions.Def_LocalPush_PageRank
import Definitions.Def_LocalPush_Layout
import Definitions.Def_LocalPush_Supplement_Spectral
import Definitions.Def_LocalPush_Supplement_QueryAlg

open Finset Matrix

namespace LocalPush

namespace Supplement

/-- **Theorem 7.1 (query lower bound for single-pair PageRank).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §7.1, Theorem 7.1, p.38
(PDF p.38).

"For every choice of integers n ≤ m ≤ n², prescribed degrees 1 ≤ d(s), d(t) ≤ n, 0 < α ≤ 1/2, and a threshold
satisfying 0 < θ ≤ min{1, d(t)/d(s)}, there is a family of unweighted, undirected simple graphs with Θ(n)
nodes, Θ(m) edges, and distinct nodes s, t of degrees d(s), d(t), respectively, for which estimating prα(s, t)
with additive error at most 10^{−9} · max{prα(s, t), θ} with success probability at least 2/3 on every input
requires Ω(min{m, (1/α^{1/2})√(d(t)/θ), min{1, d(t)/d(s)}/(αθ), d(t)/θ}) (43) expected queries in the worst
case. The algorithm can be given the values of n and m, can use degree queries, neighbor queries, adjacency
queries, and uniform node samples, and can also access the neighbor lists sorted by degree."

There are universal constants `c > 0` (the `Ω`) and `0 < c₁, C₁` (the `Θ`) such that for all integers
`n ≤ m ≤ n²`, `1 ≤ d_s, d_t ≤ n` and reals `0 < α ≤ 1/2`, `0 < θ ≤ min{1, d_t/d_s}` there is a finite
nonempty family of inputs, each a simple graph without isolated nodes given by adjacency lists sorted by
nondecreasing degree, with `c₁n ≤ |V| ≤ C₁n`, `c₁m ≤ |E| ≤ C₁m` and distinct marked nodes `s, t` of degrees
`d_s, d_t`, such that every randomized adaptive query algorithm (`QueryAlg`) that succeeds with probability
at least `2/3` on every input of the family has expected query count at least `c·min{m, …, d_t/θ}` on some
input of the family.

**Formalization Note.**
* The algorithm is quantified after the family, so it may depend on `n`, `m`, the parameters and the family
  itself; this covers "can be given the values of n and m". Sorted access is a property of the family's
  lists (nondecreasing degree; with degree queries this is equivalent to nonincreasing order).
* Graphs may be disconnected, as the Remark on p.38 requires. They have no isolated nodes (`IsAdjList`, the
  standing assumption of p.4).
* "Success" is: halt with an output `y` with `|y − pr_α(s, t)| ≤ 10⁻⁹·max{pr_α(s, t), θ}`; the expected query
  count is `∞` for an algorithm that fails to halt with positive probability. -/
theorem theorem_7_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ 0 < C₁ ∧
      ∀ (n m ds dt : ℕ) (α θ : ℝ), n ≤ m → m ≤ n ^ 2 → 1 ≤ ds → ds ≤ n → 1 ≤ dt → dt ≤ n →
        0 < α → α ≤ 1 / 2 → 0 < θ → θ ≤ min 1 ((dt : ℝ) / ds) →
        ∃ fam : Set QInput, fam.Finite ∧ fam.Nonempty ∧
          (∀ I ∈ fam, IsAdjList I.nbrs ∧ I.s ≠ I.t ∧
            (I.nbrs I.s).length = ds ∧ (I.nbrs I.t).length = dt ∧
            c₁ * n ≤ (I.N : ℝ) ∧ (I.N : ℝ) ≤ C₁ * n ∧
            c₁ * m ≤ (numEdges (toGraph I.nbrs) : ℝ) ∧ (numEdges (toGraph I.nbrs) : ℝ) ≤ C₁ * m ∧
            ∀ v, (I.nbrs v).Pairwise fun a b => (I.nbrs a).length ≤ (I.nbrs b).length) ∧
          ∀ A : QueryAlg, A.IsMeasurable →
            (∀ I ∈ fam, Succeeds A I fun y =>
              |y - pr (toGraph I.nbrs) α (e I.s) I.t| ≤
                (1 / 10 ^ 9 : ℝ) * max (pr (toGraph I.nbrs) α (e I.s) I.t) θ) →
            ∃ I ∈ fam, ENNReal.ofReal (c * min (m : ℝ)
              (min (Real.sqrt ((dt : ℝ) / θ) / Real.sqrt α)
                (min (min 1 ((dt : ℝ) / ds) / (α * θ)) ((dt : ℝ) / θ)))) ≤ qcost A I := by sorry

end Supplement

end LocalPush
