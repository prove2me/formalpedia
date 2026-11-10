-- Prove2me | Theorems.Thm_LoadBalMatch_Main_theorem_3
-- name    : LoadBalMatch.Main.theorem_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T03:33:27.331198+00:00
-- url     : https://prove2.me/theorems/b809a154-43af-40e6-b435-3199c3924f88
-- title:
--   Theorem 3 — randomized $(1-\varepsilon)$-approximate matching in general graphs with $O(\sqrt{\log n}/\varepsilon)$ passes and $\widetilde O(n/\varepsilon)$ space
-- statement:
--   In the semi-streaming model the edges of an $n$-vertex graph $G$ arrive in an arbitrary order, the same in every pass, and an algorithm is charged for the bits of memory it retains. There are constants $C>0$, $c>0$ and $k\in\mathbb N$ and, for every $n$ and every $\varepsilon\in(0,1)$, a randomized multi-pass streaming machine $\mathcal A(n,\varepsilon)$ with $s(n,\varepsilon)$ bits of memory and $P(n,\varepsilon)$ passes such that
--   $$s(n,\varepsilon)\le C\,\frac{(n+2)\log_2^k(n+2)}{\varepsilon},\qquad P(n,\varepsilon)\le C\,\frac{\sqrt{\log_2(n+2)}}{\varepsilon},$$
--   and for every simple graph $G$ (not necessarily bipartite) on the vertex set $\{0,\dots,n-1\}$ and every edge stream $\sigma$ of $G$,
--   $$\Pr\big[\mathcal A(n,\varepsilon)\text{ on }\sigma\text{ outputs a matching } M \text{ of } G \text{ with } |M|\ge(1-\varepsilon)\mu(G)\big]\ \ge\ 1-e^{-cn}.$$
--
--   This is the paper's main result: the first improvement of the $O(\log n/\varepsilon)$ pass bound of Ahn and Guha for $(1-\varepsilon)$-approximate maximum matching, here for general graphs.
--
--   **Formalization Note.** The machine is `MultiPassMachine n s P` (memory `Fin (2^s)`, input-independent initial law, a transition kernel that sees only the memory and the current edge, an end-of-pass kernel, an output kernel); it is given no pass index, stream position, edge count or graph. The constants are chosen before $n$, $\varepsilon$, $G$ and $\sigma$.
--
--   Differences from the source:
--   - encoding: a semi-streaming algorithm given G and ε → a family A n ε of MultiPassMachine n (s n ε) (P n ε): memory Fin (2^s), kernels for initial state, edge step, end of pass and output; reason: the paper restricts only space and passes; computation and fresh randomness are free, every retained bit is counted
--   - reading: Õ(n/ε) space and O(√log(n)/ε) passes → ∃ C, k fixed in advance: s ≤ C·(n+2)·log₂(n+2)^k/ε and P ≤ C·√(log₂(n+2))/ε for all n, ε; reason: Õ(n) := O(n·polylog n) (p. 1); n+2 inside the bounds only avoids log 0 and √log 1 = 0 at n ≤ 1 and agrees with n, log n up to constants for n ≥ 2
--   - reading: with exponentially high probability (footnote 2: at least 1 − exp(−Θ(n))) → probability at least 1 − exp(−c·n) with c > 0 fixed in advance, on every graph and stream; reason: the lower half of Θ(n) is the content of the claim
--   - reading: uses Õ(n/ε) space … and with exponentially high probability, outputs … → space and passes are worst-case bounds of the machine; the probability bound is on the output; reason: the literal reading of the sentence
--   - encoding: an n-vertex graph and its stream → SimpleGraph (Fin n) and a duplicate-free list of its edges (IsEdgeStream); reason: Lean convention; same instances
-- source:
--   Assadi, Bernstein, Wrzos-Kaminska, Better Bounds for Semi-Streaming Maximum Matching via Load Balancing, STOC 2027 submission (sha256 7cd28a8b…), p. 2, Theorem 3 (restated p. 44; proof pp. 48-49)

import Mathlib
import Definitions.Def_LoadBalMatch_Main_Matching
import Definitions.Def_LoadBalMatch_Main_StreamingMachine

namespace LoadBalMatch.Main

theorem theorem_3 :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ k : ℕ, ∃ s P : ℕ → ℝ → ℕ,
      ∃ A : (n : ℕ) → (ε : ℝ) → MultiPassMachine n (s n ε) (P n ε),
        ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
          (s n ε : ℝ) ≤ C * ((n : ℝ) + 2) * Real.logb 2 ((n : ℝ) + 2) ^ k / ε ∧
          (P n ε : ℝ) ≤ C * Real.sqrt (Real.logb 2 ((n : ℝ) + 2)) / ε ∧
          ∀ (G : SimpleGraph (Fin n)) (σ : List (Sym2 (Fin n))), IsEdgeStream G σ →
            ENNReal.ofReal (1 - Real.exp (-c * n)) ≤ successProb (A n ε) G σ ε := by sorry

end LoadBalMatch.Main
