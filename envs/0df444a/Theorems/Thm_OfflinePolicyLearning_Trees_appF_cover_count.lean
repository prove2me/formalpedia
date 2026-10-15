-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_appF_cover_count
-- name    : OfflinePolicyLearning.Trees.appF_cover_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:37:16.618352+00:00
-- url     : https://prove2.me/theorems/909be43f-8fbc-4ce0-8427-d8800742f562
-- title:
--   App. F, Step 2, p. 69 — at most p^{2^L−1}⌈L/ε⌉^{2^L−1}d^{2^L} trees ε-cover Π_L on any n points
-- statement:
--   Let $p,d,L\ge1$, $\varepsilon>0$, and let $x_1,\dots,x_n\in\mathbb R^p$ with $n\ge1$ (repetitions allowed). Then there are
--   $$N=p^{2^L-1}\,\lceil L/\varepsilon\rceil^{2^L-1}\,d^{2^L}$$
--   depth-$L$ trees $\pi_1,\dots,\pi_N\in\Pi_L$ (not necessarily distinct) such that every depth-$L$ tree $\pi\in\Pi_L$ satisfies $H(\pi,\pi_i)\le\varepsilon$ for some $i$, where $H$ is the Hamming distance with respect to $x_1,\dots,x_n$. In particular $N_H(\varepsilon,\Pi_L,\{x_1,\dots,x_n\})\le N$.
--
--   The count is the number of ways to choose a split variable and one of $\lceil L/\varepsilon\rceil$ thresholds at each of at most $2^L-1$ branch nodes and an action at each of at most $2^L$ leaves.
--
--   **Formalization Note** The cover is given as a family indexed by `Fin N` whose members all lie in $\Pi_L$ (a proper cover, as in Definition 4). With the depth convention of §6.1 a depth-$L$ tree has only $2^{L-1}-1$ branch nodes and $2^{L-1}$ leaves; the paper's appendix counts $2^L-1$ and $2^L$, so the printed count is an over-count and the statement remains as printed.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 69, App. F, Step 2, display N_H(ε, Π_L, {x_1,…,x_n}) ≤ p^{2^L−1}⌈L/ε⌉^{2^L−1}d^{2^L}

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Trees_Setting

namespace OfflinePolicyLearning.Trees

/-- App. F, Step 2, p. 69: for any `n ≥ 1` points `x_1, …, x_n ∈ ℝ^p`, at most
`p^{2^L-1} ⌈L/ε⌉^{2^L-1} d^{2^L}` depth-`L` trees approximate every depth-`L` tree within
`ε`-Hamming distance with respect to `x_1, …, x_n`. -/
theorem appF_cover_count (p d L : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d) (hL : 1 ≤ L) (ε : ℝ)
    (hε : 0 < ε) (n : ℕ) (hn : 1 ≤ n) (x : Fin n → (Fin p → ℝ)) :
    ∃ c : Fin (p ^ (2 ^ L - 1) * ⌈(L : ℝ) / ε⌉₊ ^ (2 ^ L - 1) * d ^ (2 ^ L)) →
        ((Fin p → ℝ) → Fin d),
      (∀ i, c i ∈ treePolicies p d L) ∧
        ∀ π ∈ treePolicies p d L, ∃ i, OfflinePolicyLearning.Regret.hammingDist x π (c i) ≤ ε := by sorry

end OfflinePolicyLearning.Trees
