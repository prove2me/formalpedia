-- Prove2me | Theorems.Thm_LocalPush_Supplement_theorem_6_1
-- name    : LocalPush.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:20:29.622191+00:00
-- url     : https://prove2.me/theorems/996d84ed-f7fb-4fc4-b938-75ec2dc7af45
-- title:
--   Theorem 6.1 — single-pair PageRank with error $\epsilon\max\{\mathrm{pr}_\alpha(s,t),\theta\}$: expected queries and expected time (corrected: additive constant)
-- statement:
--   Let $G$ be a finite simple undirected graph without isolated nodes (possibly disconnected), given by adjacency lists, with $n$ nodes, $m$ edges and degrees $d(\cdot)$, and let $\mathrm{pr}_\alpha(s,t)$ be the PageRank value of $t$ for the seed $s$. Write $\mathrm L(x)=\max\{1,\log x\}$. Both of the following hold.
--
--   1. **Queries.** There are a program $P$ of the sampling machine and $C>0$ such that for every such graph, all distinct nodes $s,t$, all $\alpha,\epsilon\in(0,1)$ and every $\theta>0$: with probability at least $2/3$ the run of $P$ on input $(s,t,\alpha,\epsilon,\theta)$ halts with an output $\hat p$ satisfying $|\hat p-\mathrm{pr}_\alpha(s,t)|\le\epsilon\max\{\mathrm{pr}_\alpha(s,t),\theta\}$, and its expected number of graph queries is at most
--   $$C\Big(1+\min\Big\{m,\ \frac1{\epsilon\alpha^{1/2}}\sqrt{\frac{d(t)}\theta},\ \frac{\min\{1,d(t)/d(s)\}}{\epsilon^2\alpha\theta},\ \frac{d(t)}{\epsilon\theta}\Big\}\Big).$$
--   2. **Time.** There are a program $P'$, $C'>0$ and an exponent $k$ with the same success guarantee and expected running time at most
--   $$C'\Big(1+\min\Big\{m,\ \frac1{\epsilon\alpha^{3/4}}\sqrt{\frac{d(t)}\theta},\ \frac{\min\{1,d(t)/d(s)\}}{\epsilon^2\alpha\theta},\ \frac{d(t)}{\epsilon\sqrt\alpha\,\theta},\ \frac{d(t)^2}{\epsilon^2\theta^2}\Big\}\,\mathrm L\Big(\frac n{\alpha\epsilon\theta}\Big)^k\Big).$$
--
--   The query bound is matched by the lower bound of Theorem 7.1; the time bound improves on bidirectional estimation with the original local push by using ActiveSetPush as the push primitive.
--
--   **Formalization Note** The programs receive only $s,t,\alpha,\epsilon,\theta$; expectations are over the fair-coin tape and the uniform tape of the sampling machine, with a non-halting run counted as $+\infty$.
--
--   Differences from the source:
--   - correction: O(min{m, …, d(t)/(ϵθ)}) expected graph queries; expected time O(min{…} polylog(n/(αϵθ))) → expected queries ≤ C·(1 + min{m, …, d(t)/(ϵθ)}); expected work ≤ C′·(1 + min{…}·L(n/(αϵθ))^k); reason: the printed bounds are false: with α = ϵ = 1/2, θ = 10⁻³ the term min{1, d(t)/d(s)}/(ϵ²αθ) = 8000/d(s) tends to 0 on graphs with d(t) = 1 and d(s) → ∞ (where pr_α(s, t) ≤ 1/d(s)), while on the one-edge graph s–t (pr_α(s, t) = 1/3) the correct outputs are disjoint; an algorithm acts identically on both until its first query, so success 2/3 on both forces a query with probability ≥ 1/3, i.e. expected queries ≥ 1/3; and every run takes at least one step
--   - reading: "can be achieved using … expected graph queries, or in expected time …" → a conjunction of two existence claims, each with its own program and constant; reason: the paper proves the two bounds with different algorithms (original local push for queries, ActiveSetPush for time, p.31)
--   - reading: "an algorithm"; sampling a random neighbour at O(1) cost → one admissible program of the sampling machine (base machine plus a unit-cost uniform random integer); time = work, queries = deg/nbr oracle calls; reason: the paper charges O(1) per random-walk step (p.31), which needs uniform integers; the base machine is the published goal's reading
--   - reading: polylog(n/(αϵθ)), O(·) → L(n/(αϵθ))^k with L = clog, k and C chosen with the program before the graph and all parameters; reason: the usual meaning, with a constant uniform in α, ϵ, θ
--   - encoding: success probability at least 2/3; expected cost → a measurable set of tapes of joint probability ≥ 2/3 on which the run halts with a correct output; expectations of the counters at the first halting step (∞ if it never halts) over the joint tape; reason: the standard probability space of the machine's randomness
--   - encoding: an undirected graph, nodes s, t, an estimate → adjacency lists satisfying IsAdjList (no isolated nodes, the standing assumption of p.4); input layout pairInput; output real memory at −1; reason: a fixed representation of the same instances; the program is not given n, m or the lists
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §6.1, Theorem 6.1, p.30 (PDF p.30)

import Mathlib
import Definitions.Def_LocalPush_PageRank
import Definitions.Def_LocalPush_Layout
import Definitions.Def_LocalPush_Supplement_SampleMachine
import Definitions.Def_LocalPush_Supplement_Inputs
import Definitions.Def_LocalPush_Supplement_Spectral

open Finset Matrix

namespace LocalPush

namespace Supplement

/-- **Theorem 6.1 (single-pair PageRank: expected queries and expected time) (corrected: additive constant
in both bounds).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §6.1, Theorem 6.1, p.30
(PDF p.30).

"For undirected graphs, given distinct nodes s, t, α, ϵ ∈ (0, 1), and θ > 0, estimating prα(s, t) with
additive error at most ϵ · max{prα(s, t), θ} with success probability at least 2/3 can be achieved using
O(min{m, (1/(ϵα^{1/2}))√(d(t)/θ), min{1, d(t)/d(s)}/(ϵ²αθ), d(t)/(ϵθ)}) expected graph queries, or in
expected time O(min{m, (1/(ϵα^{3/4}))√(d(t)/θ), min{1, d(t)/d(s)}/(ϵ²αθ), d(t)/(ϵ√α θ), d(t)²/(ϵ²θ²)}
polylog(n/(αϵθ)))."

Two claims, each with its own program of the sampling machine (`SampleMachine`) and its own constant:
1. (queries) a program `P` and `C > 0` such that on every graph (`IsAdjList`), all distinct `s, t` and all
   `α, ϵ ∈ (0, 1)`, `θ > 0`, the run on input `(s, t, α, ϵ, θ)` halts with output within
   `ϵ·max{pr_α(s, t), θ}` of `pr_α(s, t)` on a measurable event of probability at least `2/3`, and its
   expected number of graph queries is at most `C·(1 + min{m, …, d(t)/(ϵθ)})`;
2. (time) a program `P'`, `C' > 0` and an exponent `k` with the same success guarantee and expected work at
   most `C'·(1 + min{m, …, d(t)²/(ϵ²θ²)}·L(n/(αϵθ))^k)`, `L = clog`.

**Formalization Note.**
* `m` is the number of edges of the input graph and `n` its number of nodes; the program is given neither.
  `d(v)` is the degree. Graphs may be disconnected; they have no isolated nodes (p.4).
* The query count of claim 1 has no polylogarithmic factor, as printed.
* Correction: each bound is read as `C·(1 + ·)`. Fix `α = ϵ = 1/2`, `θ = 10⁻³`; the query term
  `min{1, d(t)/d(s)}/(ϵ²αθ)` tends to `0` along graphs with `d(t) = 1`, `d(s) → ∞` (where `0` is a correct
  answer), while on a graph where `pr_α(s, t) ≥ 1/10` the answer `0` is wrong; an algorithm that makes no
  query with probability `q` behaves identically on both, so success `2/3` on both forces probability at
  least `1/3` of making a query, i.e. expected queries at least `1/3` on every such input. Time is at least
  one step on every run.
* Expectations are over the joint tape (fair coins and uniform reals), of the counters at the first halting
  step, `∞` if the run does not halt. -/
theorem theorem_6_1 :
    (∃ P : SProgram, SAdmissible P ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (nbrs : Fin n → List (Fin n)), IsAdjList nbrs →
      ∀ (s t : Fin n), s ≠ t → ∀ (α ϵ θ : ℝ), 0 < α → α < 1 → 0 < ϵ → ϵ < 1 → 0 < θ →
        (∃ E : Set ((ℕ → Bool) × (ℕ → unitInterval)), MeasurableSet E ∧ (2 / 3 : ENNReal) ≤ jointTape E ∧
          ∀ p ∈ E, ∃ k : ℕ,
            (srun P nbrs (pairInput s t α ϵ θ) p.1 p.2 k).st.halted = true ∧
            |outReal (srun P nbrs (pairInput s t α ϵ θ) p.1 p.2 k).st - pr (toGraph nbrs) α (e s) t| ≤
              ϵ * max (pr (toGraph nbrs) α (e s) t) θ) ∧
        expQueries P nbrs (pairInput s t α ϵ θ) ≤
          ENNReal.ofReal (C * (1 + min (numEdges (toGraph nbrs) : ℝ)
            (min (Real.sqrt (deg (toGraph nbrs) t / θ) / (ϵ * Real.sqrt α))
              (min (min 1 (deg (toGraph nbrs) t / deg (toGraph nbrs) s) / (ϵ ^ 2 * α * θ))
                (deg (toGraph nbrs) t / (ϵ * θ))))))) ∧
    (∃ P : SProgram, SAdmissible P ∧ ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (n : ℕ) (nbrs : Fin n → List (Fin n)), IsAdjList nbrs →
      ∀ (s t : Fin n), s ≠ t → ∀ (α ϵ θ : ℝ), 0 < α → α < 1 → 0 < ϵ → ϵ < 1 → 0 < θ →
        (∃ E : Set ((ℕ → Bool) × (ℕ → unitInterval)), MeasurableSet E ∧ (2 / 3 : ENNReal) ≤ jointTape E ∧
          ∀ p ∈ E, ∃ k : ℕ,
            (srun P nbrs (pairInput s t α ϵ θ) p.1 p.2 k).st.halted = true ∧
            |outReal (srun P nbrs (pairInput s t α ϵ θ) p.1 p.2 k).st - pr (toGraph nbrs) α (e s) t| ≤
              ϵ * max (pr (toGraph nbrs) α (e s) t) θ) ∧
        expWork P nbrs (pairInput s t α ϵ θ) ≤
          ENNReal.ofReal (C * (1 + min (numEdges (toGraph nbrs) : ℝ)
            (min (Real.sqrt (deg (toGraph nbrs) t / θ) / (ϵ * α ^ (3 / 4 : ℝ)))
              (min (min 1 (deg (toGraph nbrs) t / deg (toGraph nbrs) s) / (ϵ ^ 2 * α * θ))
                (min (deg (toGraph nbrs) t / (ϵ * Real.sqrt α * θ))
                  (deg (toGraph nbrs) t ^ 2 / (ϵ ^ 2 * θ ^ 2))))) *
            clog ((n : ℝ) / (α * ϵ * θ)) ^ k))) := by sorry

end Supplement

end LocalPush
