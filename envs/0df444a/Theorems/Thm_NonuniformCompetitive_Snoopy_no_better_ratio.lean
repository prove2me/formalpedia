-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_no_better_ratio
-- name    : NonuniformCompetitive.Snoopy.no_better_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:49:13.321971+00:00
-- url     : https://prove2.me/theorems/ba3ed5c9-fb66-4a60-937b-4ff345a39805
-- title:
--   Theorem 4 (first claim) — no snoopy-caching algorithm beats $e_p/(e_p-1)$ against an oblivious adversary
-- statement:
--   Consider the single-block snoopy-caching task system with $n \ge 2$ processors and block-transfer cost $p \ge 1$ (block size $p-1$), and fix any initial state $s_0$ (the block shared, or private to one cache). If a randomized on-line algorithm $A$ is $c$-competitive against an oblivious adversary from $s_0$, that is, for some constant $a$ and every admissible request sequence $\sigma$,
--   $$\mathbf{E}C_A(\sigma) \le c\cdot C_{opt}(s_0,\sigma) + a,$$
--   then
--
--   $$c \ge \frac{e_p}{e_p - 1}, \qquad e_p = \left(1 + \frac1p\right)^p .$$
--
--   This is the lower-bound half of Theorem 4. It applies to every randomized algorithm, not only to phase-based ones, and hence also to deterministic algorithms (point-mass distributions).
--
--   **Formalization Note** The hypothesis $n \ge 2$ is needed: with a single processor the block can stay private at no cost. Theorem 4 concerns a system with many blocks; its proof reduces it to one block (p. 551), which is what is stated. Competitiveness is required only on admissible sequences (every write of processor $i$ directly follows a read or write of $i$), the paper's standing assumption that every write is preceded by a read.
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), p. 551, Theorem 4, first claim (lower bound)

import Mathlib
import Definitions.Def_NonuniformCompetitive_Snoopy_ep
import Definitions.Def_NonuniformCompetitive_Snoopy_model
import Definitions.Def_NonuniformCompetitive_Snoopy_randomized

namespace NonuniformCompetitive.Snoopy

/-- Theorem 4, first claim (Karlin et al. 1994, p. 551): in the single-block snoopy-caching
task system with `n ≥ 2` processors and block-transfer cost `p ≥ 1`, no randomized on-line
algorithm is competitive against an oblivious adversary within a factor less than
`e_p / (e_p − 1)`: from every initial state `s₀`, if `A` is `c`-competitive from `s₀` on
admissible request sequences, then `c ≥ e_p / (e_p − 1)`. -/
theorem no_better_ratio (n p : ℕ) (hn : 2 ≤ n) (hp : 1 ≤ p) (s₀ : State n)
    (A : RandomizedAlgorithm n p) (c : ℝ) (hA : A.IsCompetitiveFrom s₀ c) :
    ep p / (ep p - 1) ≤ c := by sorry

end NonuniformCompetitive.Snoopy
