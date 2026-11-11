-- Prove2me | Theorems.Thm_IPEComm1531_Main_theorem_1_1
-- name    : IPEComm1531.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:43.145111+00:00
-- url     : https://prove2.me/theorems/914b16aa-1c2e-4647-bb33-24b19170df90
-- title:
--   Theorem 1.1 — a total function family with $R(F_n)=O(\log n)$ and $\mathrm{rect}(F_n)\le2^{-\Omega(n)}$
-- statement:
--   There is a family of total Boolean functions $F_n:\{0,1\}^n\times\{0,1\}^n\to\{0,1\}$ satisfying
--   $$R(F_n)=O(\log n)\qquad\text{and}\qquad\mathrm{rect}(F_n)\le2^{-\Omega(n)} .$$
--   Explicitly: there are constants $C,c>0$ and $N$ such that for every $n\ge N$, (1) a public-coin protocol with at most $C\log_2n$ bits computes $F_n$ with error at most $1/3$ on every input, and (2) every rectangle $A\times B$ on which $F_n$ is constant has $|A||B|/2^{2n}\le2^{-cn}$.
--
--   By the product method of Impagliazzo and Williams, the second property gives $P^{NP}(F_n)=\Omega(n)$, so randomized communication is not contained in $P^{NP}$ for total functions.
--
--   Differences from the source:
--   - encoding: R(F_n) = O(log n) → ∃ C > 0, N such that for n ≥ N a public-coin protocol sending exactly k ≤ C log₂ n bits has Bob output F_n(x, y) with probability ≥ 2/3 on every input; reason: definition of R (§2) and of O(·); worst-case cost k equals exactly k bits after padding
--   - encoding: rect(F_n) ≤ 2^{−Ω(n)} → ∃ c > 0 (same N) such that every monochromatic A × B has |A||B|/2^{2n} ≤ 2^{−cn}; reason: rect is a maximum over finitely many rectangles; one threshold for both clauses is the larger of two thresholds
-- source:
--   Haoyu Wang, Pei Wu, Efficient Randomized Communication Without Large Monochromatic Rectangles, STOC 2027 submission #1531 (October 2026), PDF sha256 b5961a61deb8c9214217a3a78e8963de31cc748f73e562aad19dd584eb9eb136, Theorem 1.1, p.2

import Mathlib
import Definitions.Def_IPEComm1531_Main_Basic
import Definitions.Def_IPEComm1531_Main_Protocol
open DistVerif.Simulation

namespace IPEComm1531.Main

/-- Theorem 1.1, p.2: one family of total Boolean functions with `R(F_n) = O(log n)` and
`rect(F_n) ≤ 2^{-Ω(n)}`. -/
theorem theorem_1_1 :
    ∃ F : (n : ℕ) → (Fin n → Bool) → (Fin n → Bool) → Bool,
      ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (∃ k : ℕ, (k : ℝ) ≤ C * Real.logb 2 n ∧
          ∃ P : PubProtocol n, BobComputesWithin P k (F n) (1 / 3)) ∧
        (∀ A B : Finset (Fin n → Bool), Monochromatic (F n) A B →
          rectangleDensity A B ≤ (2 : ℝ) ^ (-(c * n))) := by sorry

end IPEComm1531.Main
