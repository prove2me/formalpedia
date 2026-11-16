-- Prove2me | Theorems.Thm_LocalPush_Supplement_theorem_6_3
-- name    : LocalPush.Supplement.theorem_6_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:21:07.645963+00:00
-- url     : https://prove2.me/theorems/2a197e82-f788-4c07-a88b-028ab8574f32
-- title:
--   Theorem 6.3 — single-pair effective resistance with additive error $\epsilon$ given $\gamma\le\nu_2$: expected queries and expected time (corrected: additive constant)
-- statement:
--   Let $G$ be a finite connected simple undirected graph, given by adjacency lists, with $m$ edges and degrees $d(\cdot)$; let $R(s,t)=(e_s-e_t)^\top L^{+}(e_s-e_t)$ be the effective resistance and $\nu_2(G)$ the spectral gap of the normalized Laplacian $D^{-1/2}LD^{-1/2}$. Write $\mathrm L(x)=\max\{1,\log x\}$. Both of the following hold.
--
--   1. **Queries.** There are a program $P$ of the sampling machine, $C>0$ and an exponent $k$ such that for every such graph, all distinct nodes $s,t$, every $\gamma$ with $0<\gamma\le\nu_2(G)$ and every $\epsilon\in(0,1]$: with probability at least $2/3$ the run of $P$ on input $(s,t,\gamma,\epsilon)$ halts with an output $\hat R$ satisfying $|\hat R-R(s,t)|\le\epsilon$, and its expected number of graph queries is at most
--   $$C\Big(1+\min\Big\{m,\ \gamma^{-1}\epsilon^{-2/3},\ \frac{\gamma^{-3}\epsilon^{-2}}{\min\{d(s),d(t)\}^2}\Big\}\,\mathrm L\Big(\frac1{\gamma\epsilon}\Big)^k\Big).$$
--   2. **Time.** There are a program $P'$, $C'>0$ and $k'$ with the same success guarantee and expected running time at most
--   $$C'\Big(1+\min\Big\{m,\ \gamma^{-4/3}\epsilon^{-2/3},\ \frac{\gamma^{-3}\epsilon^{-2}}{\min\{d(s),d(t)\}^2}\Big\}\,\mathrm L\Big(\frac1{\gamma\epsilon}\Big)^{k'}\Big).$$
--
--   The query bound matches the lower bound of Theorem 7.4 up to logarithmic factors.
--
--   **Formalization Note** The programs receive $\gamma$, not $\nu_2(G)$, and never $n$, $m$ or the lists. Expectations are over both tapes of the sampling machine, with a non-halting run counted as $+\infty$.
--
--   Differences from the source:
--   - correction: O(min{m, γ⁻¹ϵ^{−2/3}, γ⁻³ϵ⁻²/min{d(s), d(t)}²} polylog(1/(γϵ))) expected queries, and the analogous expected time → C·(1 + min{…}·L(1/(γϵ))^k) for both; reason: the printed bounds are false: with γ = 1, ϵ = 1/10, on the complete graph K_N (ν₂ = N/(N − 1), R = 2/N) the bound is at most C·100/(N − 1)²·L(10)^k → 0, while on K_2 (ν₂ = 2, R = 1) the correct outputs are disjoint for N ≥ 10, so success 2/3 on both forces a query with probability ≥ 1/3; and every run takes at least one step
--   - reading: "can be achieved using … expected graph queries, or in expected time …" → a conjunction of two existence claims, each with its own program, constant and exponent; reason: the paper proves them with different push primitives (p.37)
--   - reading: "an algorithm" in the adjacency-list model with O(1)-cost random-walk steps → one admissible program of the sampling machine; time = work, queries = deg/nbr oracle calls; reason: as in Theorem 6.1
--   - reading: polylog(1/(γϵ)), O(·) → L(1/(γϵ))^k with L = clog, k and C chosen with the program before the graph and all parameters; reason: the usual meaning, uniform in γ, ϵ
--   - encoding: ν₂(D^{−1/2}LD^{−1/2}) → nu2 G := inf{gᵀLg/gᵀDg : g ≠ 0, dᵀg = 0}; reason: the variational characterization stated on p.15 as equal to the eigenvalue; with s ≠ t and no isolated nodes the set is nonempty and bounded below by 0
--   - encoding: L⁺, the pseudoinverse → the published operator Moore–Penrose pseudoinverse HarmonicGames.Decomposition.pinv of x ↦ Lx on Euclidean ℝ^V; reason: for a matrix this is the matrix Moore–Penrose pseudoinverse
--   - encoding: success probability at least 2/3; expected cost; a connected graph, nodes s, t → a measurable set of joint tapes of probability ≥ 2/3 with halting and a correct output; expectations of the counters at the first halting step (∞ if none); adjacency lists with IsAdjList and Connected; input layout erInput; output real memory at −1; reason: a fixed representation of the same instances and of the machine's randomness
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §6.2, Theorem 6.3, p.32 (PDF p.32); R(s, t) and ν₂, §4, p.15

import Mathlib
import Definitions.Def_LocalPush_Layout
import Definitions.Def_LocalPush_Supplement_SampleMachine
import Definitions.Def_LocalPush_Supplement_Inputs
import Definitions.Def_LocalPush_Supplement_Spectral

open Finset Matrix

namespace LocalPush

namespace Supplement

/-- **Theorem 6.3 (single-pair effective resistance: expected queries and expected time) (corrected:
additive constant in both bounds).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §6.2, Theorem 6.3, p.32
(PDF p.32); `R(s, t)` and `ν₂` are defined on p.15.

"In a connected graph, given distinct nodes s, t, a spectral-gap lower bound 0 < γ ≤ ν2(D^{−1/2}LD^{−1/2}),
and an accuracy ϵ ∈ (0, 1], estimating R(s, t) with additive error at most ϵ with success probability at
least 2/3 can be achieved using O(min{m, γ^{−1}ϵ^{−2/3}, γ^{−3}ϵ^{−2}/min{d(s), d(t)}²} polylog(1/(γϵ)))
expected graph queries, or in expected time
O(min{m, γ^{−4/3}ϵ^{−2/3}, γ^{−3}ϵ^{−2}/min{d(s), d(t)}²} polylog(1/(γϵ)))."

Two claims, each with its own program of the sampling machine, constant and exponent `k`: on every connected
graph (`IsAdjList`), all distinct `s, t`, every `γ` with `0 < γ ≤ ν₂(G)` and every `ϵ ∈ (0, 1]`, the run on
input `(s, t, γ, ϵ)` halts with output within `ϵ` of `R(s, t)` on a measurable event of probability at least
`2/3`, and (1) its expected number of graph queries is at most
`C·(1 + min{m, γ⁻¹ϵ^{−2/3}, γ⁻³ϵ⁻²/min{d(s), d(t)}²}·L(1/(γϵ))^k)`, respectively (2) its expected work is at
most `C·(1 + min{m, γ^{−4/3}ϵ^{−2/3}, γ⁻³ϵ⁻²/min{d(s), d(t)}²}·L(1/(γϵ))^k)`, `L = clog`.

**Formalization Note.**
* The program receives `γ`, not `ν₂`; it is never given `n`, `m` or the lists.
* Correction: each bound is read as `C·(1 + ·)`. Take `γ = 1`, `ϵ = 1/10`. On the complete graph `K_N`
  (`ν₂ = N/(N − 1) ≥ 1`, `R(s, t) = 2/N`) the printed bound is at most `C·100/(N − 1)²·L(10)^k → 0`, while
  on `K_2` (`ν₂ = 2`, `R = 1`) the correct outputs are disjoint from those of `K_N` for `N ≥ 10`. An algorithm
  behaves identically on both until its first query, so success `2/3` on both forces a query with probability
  at least `1/3`: expected queries at least `1/3` on `K_N`. Time is at least one step on every run.
* `L⁺` is the Moore–Penrose pseudoinverse and `ν₂` the variational form of p.15 (`Spectral`). -/
theorem theorem_6_3 :
    (∃ P : SProgram, SAdmissible P ∧ ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (n : ℕ) (nbrs : Fin n → List (Fin n)), IsAdjList nbrs → (toGraph nbrs).Connected →
      ∀ (s t : Fin n), s ≠ t → ∀ (γ ϵ : ℝ), 0 < γ → γ ≤ nu2 (toGraph nbrs) → 0 < ϵ → ϵ ≤ 1 →
        (∃ E : Set ((ℕ → Bool) × (ℕ → unitInterval)), MeasurableSet E ∧ (2 / 3 : ENNReal) ≤ jointTape E ∧
          ∀ p ∈ E, ∃ j : ℕ,
            (srun P nbrs (erInput s t γ ϵ) p.1 p.2 j).st.halted = true ∧
            |outReal (srun P nbrs (erInput s t γ ϵ) p.1 p.2 j).st - effRes (toGraph nbrs) s t| ≤ ϵ) ∧
        expQueries P nbrs (erInput s t γ ϵ) ≤
          ENNReal.ofReal (C * (1 + min (numEdges (toGraph nbrs) : ℝ)
            (min (γ⁻¹ * ϵ ^ (-(2 / 3 : ℝ)))
              (γ⁻¹ ^ 3 * ϵ⁻¹ ^ 2 / min (deg (toGraph nbrs) s) (deg (toGraph nbrs) t) ^ 2)) *
            clog (1 / (γ * ϵ)) ^ k))) ∧
    (∃ P : SProgram, SAdmissible P ∧ ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (n : ℕ) (nbrs : Fin n → List (Fin n)), IsAdjList nbrs → (toGraph nbrs).Connected →
      ∀ (s t : Fin n), s ≠ t → ∀ (γ ϵ : ℝ), 0 < γ → γ ≤ nu2 (toGraph nbrs) → 0 < ϵ → ϵ ≤ 1 →
        (∃ E : Set ((ℕ → Bool) × (ℕ → unitInterval)), MeasurableSet E ∧ (2 / 3 : ENNReal) ≤ jointTape E ∧
          ∀ p ∈ E, ∃ j : ℕ,
            (srun P nbrs (erInput s t γ ϵ) p.1 p.2 j).st.halted = true ∧
            |outReal (srun P nbrs (erInput s t γ ϵ) p.1 p.2 j).st - effRes (toGraph nbrs) s t| ≤ ϵ) ∧
        expWork P nbrs (erInput s t γ ϵ) ≤
          ENNReal.ofReal (C * (1 + min (numEdges (toGraph nbrs) : ℝ)
            (min (γ ^ (-(4 / 3 : ℝ)) * ϵ ^ (-(2 / 3 : ℝ)))
              (γ⁻¹ ^ 3 * ϵ⁻¹ ^ 2 / min (deg (toGraph nbrs) s) (deg (toGraph nbrs) t) ^ 2)) *
            clog (1 / (γ * ϵ)) ^ k))) := by sorry

end Supplement

end LocalPush
