-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_optimal_ratio
-- name    : NonuniformCompetitive.Snoopy.optimal_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:50:11.828286+00:00
-- url     : https://prove2.me/theorems/2afa65c1-e344-4d36-8bac-6124ef76bfa4
-- title:
--   Theorem 4 — randomized block snoopy caching is optimally $e_p/(e_p-1)$-competitive
-- statement:
--   Consider a block snoopy-caching multiprocessor system with block size $p-1$, reduced to a single block $B$: $n \ge 2$ processors, block-transfer cost $p \ge 1$, and any initial state $s_0$ ($B$ shared, or private to one cache). Let
--
--   $$e_p = \left(1 + \frac1p\right)^p .$$
--
--   Then:
--   1. no randomized on-line algorithm is $c$-competitive against an oblivious adversary from $s_0$ for any $c < e_p/(e_p-1)$;
--   2. some randomized on-line algorithm is $e_p/(e_p-1)$-competitive against an oblivious adversary from $s_0$.
--
--   Here $c$-competitive means that for some constant $a$ and every admissible request sequence $\sigma$, $\mathbf{E}C_A(\sigma) \le c\cdot C_{opt}(s_0,\sigma) + a$. The optimal deterministic ratio for the same problem is $2$ (Karlin, Manasse, Rudolph, Sleator 1988), so randomization gives a strictly better ratio for every $p \ge 2$, tending to $e/(e-1) \approx 1.582$ as $p \to \infty$.
--
--   **Formalization Note** Three conventions are added relative to the printed statement, all from the paper's own setting. (i) $n \ge 2$: the lower bound needs a second processor. (ii) One block: the proof of Theorem 4 reduces a multi-block system to independent single-block problems (p. 551). (iii) Admissible sequences: every write of processor $i$ directly follows a read or write of $i$, the form of "every write is preceded by a read to the same block" (p. 550) that the proof uses. Both claims are stated for every initial state; the additive constant may depend on $n$, $p$ and $s_0$.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 551, Theorem 4 (single-block task system of §3.1, p. 550)

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_model
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized

namespace NonuniformCompetitive.Snoopy

/-- Theorem 4 (Karlin, Manasse, McGeoch, Owicki, Algorithmica 11 (1994), p. 551), for the
single-block snoopy-caching task system of §3.1 (p. 550) with `n ≥ 2` processors and block size
`p − 1` (block-transfer cost `p ≥ 1`), from every initial state `s₀`:
1. no randomized on-line algorithm is `c`-competitive against an oblivious adversary for any
   `c < e_p / (e_p − 1)`;
2. some randomized on-line algorithm is `e_p / (e_p − 1)`-competitive.
Competitiveness is over admissible request sequences (every write of processor `i` directly
follows a read or write of `i`). -/
theorem optimal_ratio (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n) :
    (∀ (A : RandomizedAlgorithm n p) (c : ℝ), A.IsCompetitiveFrom s₀ c → ep p / (ep p - 1) ≤ c) ∧
      ∃ A : RandomizedAlgorithm n p, A.IsCompetitiveFrom s₀ (ep p / (ep p - 1)) := by sorry

end NonuniformCompetitive.Snoopy
