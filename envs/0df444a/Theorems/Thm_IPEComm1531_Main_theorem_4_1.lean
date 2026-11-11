-- Prove2me | Theorems.Thm_IPEComm1531_Main_theorem_4_1
-- name    : IPEComm1531.Main.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:03:41.892746+00:00
-- url     : https://prove2.me/theorems/5a600a9d-16a6-4164-bfcf-e5a8495ec61e
-- title:
--   Theorem 4.1 — $R(\mathrm{IPE}_n)=O(\log n)$
-- statement:
--   Let the spaces, extractor and prescribed-zero functions satisfy the correctness conclusions of Theorem 3.2, Fact 2.3 and Lemma 3.3 (with no algorithmic effectivity assumed), and let $\mathrm{IPE}_n$ be the resulting function on $n$-bit input pairs. There are $C>0$ and $N$ such that for every $n\ge N$ some public-coin protocol with at most $C\log_2 n$ bits of communication computes $\mathrm{IPE}_n$ with error at most $1/3$ on every input:
--   $$R(\mathrm{IPE}_n)=O(\log n).$$
--
--   This is the upper-bound half of Theorem 1.1.
--
--   Differences from the source:
--   - generalization: the specific objects constructed in Fact 2.3, Theorem 3.2 and Lemma 3.3 → every family satisfying the correctness conclusions of Fact 2.3, Theorem 3.2 and Lemma 3.3, with no algorithmic effectivity required; reason: the communication and rectangle arguments use only correctness, since local computation is uncharged; the source objects satisfy these hypotheses, so the Lean statement specializes to the source
--   - encoding: R(IPE_n) = O(log n) → ∃ C > 0, N such that for n ≥ N a public-coin protocol sending exactly k ≤ C log₂ n bits has Bob output IPE_n(x, y) with probability ≥ 2/3 on every input; reason: definition of R and of O(·); worst-case cost k is the same as exactly k bits after padding; the source protocol outputs at Bob
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Theorem 4.1, p.10 (proof pp.10–11)

import Mathlib
import Definitions.Def_IPEComm1531_Main_Construction
import Definitions.Def_IPEComm1531_Main_Protocol
open DistVerif.Simulation

namespace IPEComm1531.Main

/-- Theorem 4.1 (randomized protocol for IPE), p.10. -/
theorem theorem_4_1 (S : Spaces) (E : Extractors) (p : Prescribed)
    (hS : S.Good) (hE : E.Good) (hp : PrescribedCorrect S p) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ k : ℕ, (k : ℝ) ≤ C * Real.logb 2 n ∧
        ∃ P : PubProtocol n, BobComputesWithin P k (family S E p n) (1 / 3) := by sorry

end IPEComm1531.Main
