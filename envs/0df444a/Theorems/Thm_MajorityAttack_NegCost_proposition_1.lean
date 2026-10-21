-- Prove2me | Theorems.Thm_MajorityAttack_NegCost_proposition_1
-- name    : MajorityAttack.NegCost.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:09.458757+00:00
-- url     : https://prove2.me/theorems/e26f3101-0917-44ab-a85c-1b5bcbe32b2b
-- title:
--   Proposition 1 — a sub-majority active miner can make no-attack equilibrium impossible at zero private benefit
-- statement:
--   Consider finitely many miners with nonnegative incumbent hash powers totaling $H>0$. Let $\tau>0$ be the target block interval, $\mathcal L>0$ the expected attack duration, and $R$ the common block reward. Transaction fees are independent with a common nonnegative, non-degenerate, integrable law $\mu$. A block holds $b\ge1$ transactions; an honest block has $n>b$ available transactions and a slower attack block has $n'>n$. Each miner has a nondecreasing convex cost and an attained optimizer of its attack-chain flow profit.
--
--   There is a threshold $0<\widehat h<H/2$, chosen from these model data before the incumbent allocation, such that if some active miner has $h_i^*>\widehat h$, then no no-attack equilibrium satisfies every active miner's attack incentive constraint, even when the private attack benefit is zero:
--
--   $$\exists\,\widehat h\in(0,H/2)\quad\forall(h_i^*)_i\text{ with }\sum_i h_i^*=H,\quad \bigl(i\text{ active},\ h_i^*>\widehat h\bigr)\Longrightarrow\neg\operatorname{NoAttackEquilibrium}(V)\quad(V\ge0).$$
--
--   This is Proposition 1's conclusion that congestion can make a majority attack profitable for a miner holding less than half the incumbent hash power, with nothing to gain from double-spending.
--
--   **Formalization Note** The attack-chain fee is computed from the same fee law at $n'$ arrivals, rather than assumed larger. The natural arrival counts encode the paper's slower attack chain. The incumbent powers need not optimize pre-attack profits, making this version stronger than the stated equilibrium model.
-- source:
--   Gans & Halaburda, “Zero Cost” Majority Attacks on Permissionless Blockchains, arXiv:2308.06568v1, pp. 13–14, Proposition 1

import Mathlib
import Definitions.Def_MajorityAttack_NegCost_Model

namespace MajorityAttack.NegCost

/-- Proposition 1, pp. 13–14: a sub-majority active miner above the threshold
precludes a no-attack equilibrium even with zero private benefit. -/
theorem proposition_1 {ι : Type*} [Fintype ι]
    (τ H R L : ℝ) (hτ : 0 < τ) (hH : 0 < H) (hL : 0 < L)
    (μ : MeasureTheory.Measure ℝ) (hμ : FeeLaw μ)
    (b n n' : ℕ) (hb : 0 < b) (hbn : b < n) (hnn' : n < n')
    (c : ι → ℝ → ℝ) (hc : ∀ i, CostStanding (c i))
    (htil : ι → ℝ)
    (hopt : ∀ i, IsAttackOptimum (τ * H) (R + blockFees μ b n') (c i) (htil i)) :
    ∃ hhat : ℝ, 0 < hhat ∧ hhat < H / 2 ∧
      ∀ hstar : ι → ℝ, (∀ j, 0 ≤ hstar j) → (∑ j, hstar j) = H →
        ∀ i, 0 ≤ flowProfit (τ * H) (R + blockFees μ b n) (c i) (hstar i) →
          hhat < hstar i → ∀ V : ℝ, 0 ≤ V →
            ¬ NoAttackEquilibrium τ H L R (blockFees μ b n) (blockFees μ b n')
                c htil hstar V := by sorry

end MajorityAttack.NegCost
