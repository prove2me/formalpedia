-- Prove2me | Theorems.Thm_OfflinePolicyLearning_Regret_eq48_oracle_value_unbiased
-- name    : OfflinePolicyLearning.Regret.eq48_oracle_value_unbiased
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T02:33:56.606724+00:00
-- url     : https://prove2.me/theorems/124e5122-0c31-4953-b021-85b9ebe83416
-- title:
--   (48), p. 60 — the oracle AIPW value estimate is unbiased: E[Q̃(π)] = Q(π)
-- statement:
--   Work in the potential-outcome model of the mission (features $X\sim P_X$; given $X$, the outcome vector $(Y(1),\dots,Y(d))$ and the logged action $A$ independent). Assume
--
--   1. overlap: $e_a(x)\ge\eta$ for all $x,a$, for some $\eta>0$;
--   2. bounded rewards: for every $x$, almost surely under the conditional law of the outcome vector given $X=x$, $|Y(a)|\le B$ for all $a$.
--
--   Let $\pi$ be a measurable policy and $n\ge1$. For $n$ iid draws, the oracle estimate $\tilde Q(\pi)=\frac1n\sum_{i=1}^n\langle\pi(X_i),\Gamma_i\rangle$ satisfies
--   $$\mathbb E\big[\tilde Q(\pi)\big]=Q(\pi)=\mathbb E\big[Y(\pi(X))\big].$$
--
--   Consequently $\mathbb E[\tilde\Delta(\pi_1,\pi_2)]=\Delta(\pi_1,\pi_2)$, which is what centres the oracle empirical process at the true value differences.
--
--   **Formalization Note** Unconfoundedness is built into the model's joint law. Overlap makes the division by $e_{A}(X)$ in $\Gamma_i$ honest and the score bounded; bounded rewards and measurability of $\pi$ make every expectation an integral of a bounded measurable function. Bounded support is stated for each $x$ under the conditional law, a $P_X$-null modification of the paper's joint form.
-- source:
--   Zhou, Athey & Wager, Offline Multi-Action Policy Learning, arXiv:1810.04778v2, p. 60, App. D, proof of Theorem 2, Step 1, display (48)

import Mathlib
import Definitions.Def_OfflinePolicyLearning_Regret_Hamming
import Definitions.Def_OfflinePolicyLearning_Regret_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace OfflinePolicyLearning.Regret
theorem eq48_oracle_value_unbiased {X : Type*} [MeasurableSpace X] {d : ℕ} (M : Model X d)
    (η : ℝ) (hη : 0 < η) (hover : ∀ x a, η ≤ M.e x a)
    (B : ℝ) (hB : ∀ x, ∀ᵐ y ∂(M.κY x), ∀ a, |y a| ≤ B)
    (π : X → Fin d) (hπ : Measurable π) (n : ℕ) (hn : 1 ≤ n) :
    ∫ D, M.Qtilde D π ∂M.sample n = M.Q π := by sorry
end OfflinePolicyLearning.Regret
