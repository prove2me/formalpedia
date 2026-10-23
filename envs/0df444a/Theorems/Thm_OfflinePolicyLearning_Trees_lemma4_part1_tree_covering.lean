-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_lemma4_part1_tree_covering
-- name    : OfflinePolicyLearning.Trees.lemma4_part1_tree_covering
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:37:13.59198+00:00
-- url     : https://prove2.me/theorems/d582fe4a-59d1-49fc-a717-47decc366c54
-- title:
--   Lemma 4, part 1, p. 27 — log N_H(ε, Π_L) ≤ (2^L − 1) log p + 2^L log d + (2^L − 1) log(L/ε + 1)
-- statement:
--   Let $p\ge1$ be the feature dimension, $d\ge1$ the number of actions, $L\ge1$ the tree depth, and $\varepsilon>0$. The $\varepsilon$-Hamming covering number $N_H(\varepsilon,\Pi_L)$ of the class $\Pi_L$ of depth-$L$ decision trees on $\mathbb R^p$ with $d$ actions is finite, and
--   $$\log N_H(\varepsilon,\Pi_L)\le(2^L-1)\log p+2^L\log d+(2^L-1)\log\Big(\frac L\varepsilon+1\Big).$$
--
--   For fixed $L,p,d$ the right-hand side is $O(\log(1/\varepsilon))$, so the entropy integral of $\Pi_L$ is finite and the paper's regret bound for policy learning applies to decision-tree policies.
--
--   **Formalization Note** The finiteness of $N_H(\varepsilon,\Pi_L)$ is stated as a separate conjunct: in Lean the logarithm is applied to `toNat` of an `ℕ∞` value, and `toNat ⊤ = 0` with `Real.log 0 = 0` would otherwise make the inequality hold for an infinite covering number. The trees follow §6.1 (a depth-$L$ tree has $L$ layers, $2^{L-1}-1$ branch nodes); the bound is as printed, which over-counts for this convention. The feature space is all of $\mathbb R^p$, which implies the bound for every bounded $\mathcal X\subseteq\mathbb R^p$. The paper's trailing "$=O(\log 1/\varepsilon)$" is a remark on the right-hand side and is not part of the statement.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 27, Lemma 4 (1); proof App. F, pp. 67–69

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Trees_Setting

namespace OfflinePolicyLearning.Trees

/-- Lemma 4, part 1, p. 27: `N_H(ε, Π_L)` is finite and
`log N_H(ε, Π_L) ≤ (2^L - 1) log p + 2^L log d + (2^L - 1) log(L/ε + 1)`. -/
theorem lemma4_part1_tree_covering (p d L : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d) (hL : 1 ≤ L) (ε : ℝ)
    (hε : 0 < ε) :
    OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d L) ≠ ⊤ ∧
      Real.log ((OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d L)).toNat : ℝ) ≤
        (2 ^ L - 1 : ℝ) * Real.log p + (2 : ℝ) ^ L * Real.log d +
          (2 ^ L - 1 : ℝ) * Real.log (L / ε + 1) := by sorry

end OfflinePolicyLearning.Trees
