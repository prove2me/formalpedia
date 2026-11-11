-- Prove2me | Theorems.Thm_LewensteinGreedy_Competitive_theorem_2_3
-- name    : LewensteinGreedy.Competitive.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:33:00.391027+00:00
-- url     : https://prove2.me/theorems/35d2cb21-fbed-407e-8725-33a46dafff2a
-- title:
--   Theorem 2.3 — normalized comparator: height $O(\log(n+1))$, rotations at depth $O(1)$, $R+m=O(\mathrm{OPT}_n(X))$
-- statement:
--   There are absolute constants $k\in\mathbb N$ and $C,c>0$ such that for every $n\ge1$ and every access sequence $X\in[n]^m$ there is a comparator execution serving $X$ (each designated access state has the requested key at its root) whose height is at most $C\log_2(n+1)$ in every state, all of whose rotations promote a key of depth at most $k$ (measured just before the rotation), and whose number $R$ of rotations satisfies
--   $$R+m\le c\cdot \mathrm{OPT}_n(X),$$
--   where $\mathrm{OPT}_n(X)$ is the free-initialization node-touch optimum of §2.1.1.
--
--   The source imports this normal form from [CHH+26]. The platform's Open goal `SplayDynOpt.theorem_2` (theorem_id d3a513a9-7dde-43c2-989d-4c8ebefb246d) is the related statement in that paper's root-rotation cost model, for $n\ge2$ and with extra riblessness. This item is the statement as this source uses it: the node-touch $\mathrm{OPT}_n$, all $n\ge1$ including the empty sequence. It does not restate the Open goal.
--
--   Differences from the source:
--   - reading: height O(log(n+1)) throughout, rotations at depth O(1), R + m = O(OPT_n(X)) → absolute constants C, k, c chosen before n and X: height ≤ C·log₂(n+1) at every state, promoted-key depth ≤ k before every rotation, R + m ≤ c·OPT_n(X); reason: O-notation in this paper denotes absolute constants (§5.3 "All constants are absolute"); depth of a rotation is the promoted key's pre-rotation depth, as for d_i in (2.2)
--   - encoding: absolute constants → 0 < C and 0 < c; reason: the right-hand sides are nonnegative, so positive constants exist iff any do
--   - encoding: standing universe [n] with n ≥ 1 (§1.2) → explicit hypothesis 1 ≤ n; reason: the source fixes n ≥ 1 for the whole paper
--   - encoding: keys [n] = {1,…,n}, access sequence X ∈ [n]^m → keys are naturals, [n] = Finset.Icc 1 n, X : List ℕ with ValidSequence n X (m = X.length, m = 0 allowed); reason: Lean convention; same instances
-- source:
--   Lewenstein, Greedy BST is O(log log n)-Competitive, supplied 2026 artifact (STOC 2027 submission; no DOI/arXiv/URL), SHA-256 04ac49f62855387e9d720867c8d3ded88730274553ff2fb8473a7a53b6906c4f, Theorem 2.3, printed p. 7 / PDF 8

import Mathlib
import Definitions.Def_SplayDynOpt_IsBSTOn
import Definitions.Def_SplayDynOpt_rotateAt
import Definitions.Def_LewensteinGreedy_Competitive_TouchModel
import Definitions.Def_LewensteinGreedy_Competitive_Comparator

namespace LewensteinGreedy.Competitive

/-- Theorem 2.3 (normalized comparator), printed p.7 / PDF 8: absolute constants `k, C, c` such that
every access sequence on `[n]` has a comparator serving it with every request at the root of its
designated state, height `≤ C log₂(n+1)` throughout, every rotation promoting a key of depth `≤ k`,
and `R + m ≤ c · OPT_n(X)`. -/
theorem theorem_2_3 :
    ∃ k : ℕ, ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ n : ℕ, 1 ≤ n → ∀ X : List ℕ, ValidSequence n X →
        ∃ e : Comparator, e.serves n X ∧
          (e.height n : ℝ) ≤ C * Real.logb 2 ((n : ℝ) + 1) ∧
          (∀ i < e.rotations, SplayDynOpt.depth (e.promoted i) (e.tree i) ≤ k) ∧
          ((e.rotations + X.length : ℕ) : ℝ) ≤ c * (OPT n X : ℝ) := by sorry

end LewensteinGreedy.Competitive
