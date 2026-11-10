-- Prove2me | Theorems.Thm_KoanaKPaths_Main_directed_path_counting
-- name    : KoanaKPaths.Main.directed_path_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T08:38:09.832918+00:00
-- url     : https://prove2.me/theorems/04252733-0ecb-4ebc-98aa-2e0dac60378c
-- title:
--   Theorem 1 — $(1\pm\varepsilon)$-approximate counting of directed $k$-paths in $O^*(2^k\varepsilon^{-2}\log(1/\delta))$ time
-- statement:
--   A **directed $k$-path** in a directed graph $G$ is an ordered tuple $(v_1,\dots,v_k)$ of pairwise distinct vertices such that $(v_i,v_{i+1})$ is an arc for every $1\le i<k$; let $N$ be their number.
--
--   Let $k\ge1$ and $0<\varepsilon,\delta<1$. Given a simple directed graph $G$ with $n$ vertices, there is a randomized algorithm that returns a $(1\pm\varepsilon)$-approximation $\widehat N$ to $N$,
--   $$\Pr\bigl[\,|\widehat N-N|\le\varepsilon N\,\bigr]\ge1-\delta,$$
--   and runs in $O^*(2^k\varepsilon^{-2}\log(1/\delta))$ time, where $O^*$ suppresses factors polynomial in $k$ and the input size.
--
--   Precisely: there are one randomized machine $M$ and constants $K,c$, fixed before all inputs, such that for every simple directed graph on the vertices $0,\dots,n-1$ (no loops, given by a duplicate-free list of arcs in any order), every $k\ge1$ and all real $\varepsilon,\delta\in(0,1)$, with $a=\lceil\log_2(1/\varepsilon)\rceil$, $b=\lceil\log_2(1/\delta)\rceil$, $L$ the length of the graph encoding ($n$ and the arc list, excluding $k,a,b$) and
--   $$B=K\,2^k\,(1+k+n+L)^c\,4^a\,(b+1),$$
--   for every tape of more than $B$ fair random bits, every run halts within $B$ steps, reads at most $B$ random bits and writes a rational $\widehat N$; and over the random bits the displayed accuracy event has probability at least $1-\delta$.
--
--   This resolves the conjecture of Koutis and Williams that directed $k$-paths can be approximately counted in $O^*(2^k)$ time. All graphs are included: $k>n$, graphs without $k$-paths ($N=0$, where the output must be exactly $0$ with probability at least $1-\delta$), disconnected and non-symmetric graphs.
--
--   **Formalization Note** The machine is a multi-stack Turing machine (Mathlib's `Turing.FinTM2` with finite alphabets, as in the reused fair-bit machine model), so the step count is bit time. Paths are injective maps $\{0,\dots,k-1\}\to\{0,\dots,n-1\}$ with consecutive pairs in the arc set (the reused definition `PathCount2k.N`). Since $4^a<4\varepsilon^{-2}$, $B$ is at most a constant multiple of $2^k(1+k+n+L)^c\varepsilon^{-2}(1+\log(1/\delta))$.
--
--   Differences from the source:
--   - encoding: a randomized algorithm running in O*(2^k ε^{-2} log(1/δ)) time → one fixed fair-bit FinTM2 machine and constants K, c chosen before all inputs, halting within K·2^k·(1+k+n+L)^c·4^a·(b+1) steps and random bits on every tape longer than that; reason: a FinTM2 step is a bounded fragment on finite alphabets, so steps are bit operations up to a constant, and O* hides exactly a polynomial in k and the graph size (n, L), with L excluding the tolerance controls
--   - encoding: real ε, δ given to the algorithm → the machine reads a = ⌈log₂(1/ε)⌉ and b = ⌈log₂(1/δ)⌉ while accuracy and confidence are required for the real ε, δ themselves; reason: a machine cannot read a real number; 4^a < 4ε^{-2}, so every real tolerance is covered with the same ε^{-2} dependence
--   - reading: the factor log(1/δ) → the factor b + 1 ≤ 2 + log₂(1/δ), i.e. O(1 + log(1/δ)); reason: log(1/δ) tends to 0 as δ → 1, while any algorithm takes at least one step, so the O-bound is read as O(1 + log(1/δ)), which is log(1/δ) up to a factor 3 for δ ≤ 1/2
--   - encoding: a simple directed graph G with vertex set [n] → vertices Fin n (0-based) and a duplicate-free arc list without loops, in any order, with arc set its underlying finite set; reason: a bijective relabeling; simplicity is exactly no loops and no repeated arcs
--   - encoding: the returned approximation → a written rational (binary numerator and positive denominator); reason: the algorithm's output is a rational number
-- source:
--   Tomohiro Koana, STOC 2027 submission #953 (October 2026), p. 1 (PDF p. 2), Theorem 1; repeated and proved p. 9 (PDF p. 10), Section 4.1

import Mathlib
import Definitions.Def_PathCount2k_Graph
import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_KoanaKPaths_Main_Inputs

open HypergraphUnreliability.FPRAS

namespace KoanaKPaths.Main

/-- **Theorem 1** (Koana, STOC 2027 submission #953, printed p. 1 / PDF p. 2; repeated and proved
in §4.1, printed p. 9 / PDF p. 10). One fair-bit machine `M` and constants `K, c`, fixed before all
inputs, such that for every simple directed graph on the vertices `Fin n` (no loops, a
duplicate-free arc list in any order), every `k ≥ 1` and all real `0 < ε, δ < 1`: on input the
graph, `k` and the controls `a = ⌈log₂(1/ε)⌉`, `b = ⌈log₂(1/δ)⌉`, for every tape of more than
`B = K 2^k (1 + k + n + L)^c 4^a (b + 1)` fair bits (`L` the graph encoding length, excluding `k`
and tolerance controls), every run halts within
`B` steps using at most `B` tape bits and writes a rational `N̂`, and with probability at least
`1 − δ`, `|N̂ − N| ≤ ε N`, where `N` is the number of directed `k`-vertex paths. -/
theorem directed_path_counting :
    ∃ (M : CoinMachine) (K c : ℕ), ∀ (n : ℕ) (arcs : List (Fin n × Fin n)), arcs.Nodup →
      (∀ p ∈ arcs, p.1 ≠ p.2) → ∀ k : ℕ, 1 ≤ k →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
      ∀ T : ℕ, timeBudget K c k (n + (graphCode n arcs).length) (ctrl ε) (ctrl δ) < T →
        (∀ ω : Fin T → Bool, ∃ Nhat : Frac, 0 < Nhat.den ∧
          M.RunsWithin (graphInput n arcs k ε δ) (tapeList ω)
            (timeBudget K c k (n + (graphCode n arcs).length) (ctrl ε) (ctrl δ))
            (fracCode Nhat)) ∧
        1 - δ ≤ fairProb T (fun ω => ∃ Nhat : Frac, 0 < Nhat.den ∧
          M.RunsWithin (graphInput n arcs k ε δ) (tapeList ω)
            (timeBudget K c k (n + (graphCode n arcs).length) (ctrl ε) (ctrl δ))
            (fracCode Nhat) ∧
          |((Nhat.val : ℚ) : ℝ) - (PathCount2k.N n arcs.toFinset k : ℝ)| ≤
            ε * (PathCount2k.N n arcs.toFinset k : ℝ)) := by sorry

end KoanaKPaths.Main
