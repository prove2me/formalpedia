-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Trees_appF_cover_num_le
-- name    : OfflinePolicyLearning.Trees.appF_cover_num_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:37:19.809378+00:00
-- url     : https://prove2.me/theorems/f10a7f9e-2cc9-4267-af79-9adc11e5be9b
-- title:
--   App. F, Step 2, p. 69 — N_H(ε, Π_L) ≤ p^{2^L−1}⌈L/ε⌉^{2^L−1}d^{2^L}
-- statement:
--   Let $p,d,L\ge1$ and $\varepsilon>0$. The $\varepsilon$-Hamming covering number of the class $\Pi_L$ of depth-$L$ decision trees on $\mathbb R^p$ with $d$ actions satisfies
--   $$N_H(\varepsilon,\Pi_L)\le p^{2^L-1}\,\lceil L/\varepsilon\rceil^{2^L-1}\,d^{2^L}.$$
--   In particular it is finite.
--
--   This is the uniform-over-point-sets form of the finite-sample count, and it implies the logarithmic bound of Lemma 4, part 1.
--
--   **Formalization Note** The inequality is in `ℕ∞`, where $N_H(\varepsilon,\Pi_L)$ lives; $\lceil L/\varepsilon\rceil$ is `Nat.ceil`.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 69, App. F, Step 2, "Since this is true for any set of points {x_1,…,x_n}, we have N_H(ε, Π_L) ≤ p^{2^L−1}⌈L/ε⌉^{2^L−1}d^{2^L}"

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Trees_Setting

namespace OfflinePolicyLearning.Trees

/-- App. F, Step 2, p. 69: `N_H(ε, Π_L) ≤ p^{2^L-1} ⌈L/ε⌉^{2^L-1} d^{2^L}`. -/
theorem appF_cover_num_le (p d L : ℕ) (hp : 1 ≤ p) (hd : 1 ≤ d) (hL : 1 ≤ L) (ε : ℝ)
    (hε : 0 < ε) :
    OfflinePolicyLearning.Regret.hammingCoverNum ε (treePolicies p d L) ≤
      ((p ^ (2 ^ L - 1) * ⌈(L : ℝ) / ε⌉₊ ^ (2 ^ L - 1) * d ^ (2 ^ L) : ℕ) : ℕ∞) := by sorry

end OfflinePolicyLearning.Trees
