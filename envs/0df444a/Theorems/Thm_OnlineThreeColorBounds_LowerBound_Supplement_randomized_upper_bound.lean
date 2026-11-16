-- Prove2me | Theorems.Thm_OnlineThreeColorBounds_LowerBound_Supplement_randomized_upper_bound
-- name    : OnlineThreeColorBounds.LowerBound.Supplement.randomized_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:39:22.421196+00:00
-- url     : https://prove2.me/theorems/516864e2-6958-4ddd-b3c1-cd7be860f0fb
-- title:
--   Theorem 1.2 — randomized online coloring of three-colorable graphs with $O(\sqrt n)$ expected colors in expected polynomial time
-- statement:
--   There is a randomized online coloring algorithm $A$ with the following properties. It is a single program of the logarithmic-cost RAM with fair coins, fixed in advance; it is not told the number of vertices. There are absolute constants $C,K,d\ge0$ such that for every $n$ and every three-colorable ordered graph $G$ with $m\le n$ vertices, fixed independently of the algorithm's coins:
--
--   1. on every coin tape on which the algorithm halts at every arrival, the coloring is proper: each arrival gets one color, different from the colors of its earlier neighbors;
--   2. the expected number of colors used is $O(\sqrt n)$:
--   $$\mathbb E\,C_A(G,\pi)\le C\sqrt n;$$
--   3. the algorithm runs in expected polynomial time: the expected total bit cost, summed over all arrivals, is at most $K(n+1)^d$.
--
--   The expectations are over the fair coins only, so the input is an oblivious adversary. The theorem improves Vishwanathan's randomized $O(\sqrt{n\log n})$ bound of 1990. Theorem 1.1, the goal of this mission, is a deterministic lower bound; this theorem is an independent companion result and is not used in its proof.
--
--   **Formalization Note** The algorithm is a program of the published `TimeSpaceMA_RAM`. Arrival $i$'s color is read from cell $0$ after the program runs on the encoded prefix $N^-(0),\dots,N^-(i)$ with the shared tape. Properness is the base `LegalHistory 1` of the induced history. Expectations are lower integrals against the published `coinTape`; the measurability of the color count and the total cost is stated as well, so the lower integrals are true expectations. A finite expected cost forces halting with probability one.
--
--   Differences from the source:
--   - encoding: a randomized online algorithm and its running time → one program P of the published log-cost RAM with fair coins; arrival i's color is cell 0 after running P on the encoded revealed prefix with one coin tape shared by all arrivals; time is the sum over arrivals of the published bit cost; reason: an online randomized algorithm's color for arrival i is a function of the revealed prefix and its random bits; with the shared tape the program can replay its earlier decisions, which costs at most a factor m over a stateful implementation, so expected polynomial time is unchanged; the log-cost RAM without multiplication is polynomially equivalent to the usual machine models
--   - reading: There is a randomized online algorithm A such that, for every fixed ordered three-colorable graph with at most n vertices → P is chosen before n and does not receive n or the number of vertices; reason: this is the quantifier order of the statement; §3 assumes n is known, citing Remark 1.3(1), which would be the weaker reading, and the restart-with-doubled-budget device of §3.3 removes that assumption
--   - encoding: E C_A(G, π) = O(√n) → there is an absolute C with E C_A ≤ C√n for every n and every graph with m ≤ n vertices; reason: C_A ≤ m ≤ n, so the asymptotic and the uniform forms are equivalent
--   - encoding: expected polynomial time → E[total bit cost] ≤ K(n+1)^d with absolute K, d; reason: a polynomial in the number of vertices; the encoded input has size polynomial in n, so this is the usual notion
--   - encoding: the expectation, and properness of a randomized algorithm → lower integrals against the fair-coin tape, with measurability of the color count and of the total cost as additional conjuncts, and properness on every tape on which every arrival halts; reason: the measurability conjuncts hold for every program and make the lower integrals the expectations; the source's properness argument is deterministic and holds on every outcome
--   - encoding: ordered three-colorable graph with at most n vertices → G : SimpleGraph (Fin m) with m ≤ n, G.Colorable 3, arrival order the order of Fin m; reason: arrival indices encode every finite ordered graph
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, Theorem 1.2 (Randomized upper bound), §1, printed p. 1 / PDF p. 2; proof §3, printed pp. 10–17 / PDF pp. 11–18

import Definitions.Def_OnlineThreeColorBounds_LowerBound_Supplement_RandomizedOnline
set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace OnlineThreeColorBounds.LowerBound.Supplement

open OnlineThreeColorBounds.LowerBound

/-- Theorem 1.2 (Randomized upper bound), printed p. 1 / PDF p. 2. One program `P` of the
log-cost RAM with fair coins, fixed before `n` and the input, is a randomized online coloring
algorithm (arrival `i`'s color is computed from the revealed prefix and the shared coin tape). For
every `n` and every ordered three-colorable graph `G` with `m ≤ n` vertices, fixed before the
coins: the coloring is proper on every tape on which the run halts at every arrival; the expected
number of colors is at most `C √n`; and the expected total bit cost of the run is at most
`K (n + 1) ^ d`. The constants `C, K, d` depend on nothing. -/
theorem randomized_upper_bound :
    ∃ P : TimeSpaceMA.Program, ∃ C K d : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ 0 ≤ d ∧
      ∀ n m : ℕ, m ≤ n → ∀ G : SimpleGraph (Fin m), G.Colorable 3 →
        (∀ τ : ℕ → Bool, AllHalt P G τ → LegalHistory 1 (onlineHistory P G τ)) ∧
        Measurable (colorsUsed P G) ∧
        ∫⁻ τ, (colorsUsed P G τ : ℝ≥0∞) ∂SoftmaxAttnFD.coinTape ≤
          ENNReal.ofReal (C * Real.sqrt n) ∧
        Measurable (onlineCost P G) ∧
        ∫⁻ τ, onlineCost P G τ ∂SoftmaxAttnFD.coinTape ≤
          ENNReal.ofReal (K * ((n : ℝ) + 1) ^ d) := by sorry

end OnlineThreeColorBounds.LowerBound.Supplement
