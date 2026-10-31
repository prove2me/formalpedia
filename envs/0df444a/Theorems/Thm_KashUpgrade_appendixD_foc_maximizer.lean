-- Prove2me | Theorems.Thm_KashUpgrade_appendixD_foc_maximizer
-- name    : KashUpgrade.appendixD_foc_maximizer
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:23.321576+00:00
-- url     : https://prove2.me/theorems/dd1ed339-719e-48d6-8355-c58d83d87854
-- title:
--   (20), p.17 and (40), p.51 — $\theta^{FOC}$ maximizes the joint term
-- statement:
--   Let the type law satisfy Assumption 2 and let $c>0$. Let $B$ be a finite set of indices with positive total weight, with nonnegative weights and positive intervals at the indices of positive weight. Then $\theta^{j,FOC}_B$ lies in the support, and it maximizes the joint term
--   $$
--   (1-F(\theta))\sum_{\ell\in B}A_\ell\bigl((s_\ell-s_{\ell-1})\theta-c\bigr)
--   $$
--   over the support.
--
--   This covers the boundary case: when the block's value exceeds $\zeta$, the maximizer is $\zeta$ and no customer upgrades.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (9) with the infimum over θ → infimum over (0, ζ), value in [0, ∞], real value taken; reason: v is defined on the support; the end points change nothing because of the minimum with ζ and the infimum; the value is finite under Assumption 2
--   - generalization: the block L(i) of a lumping → any finite set of indices B; reason: every block is such a set
--   - generalization: the weights of (38) and the intervals of the schedule → arbitrary nonnegative weights, where an index of positive weight has a positive interval; reason: the proof uses no more; the weights of (38) are of this kind
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (18), (20), p.17; Appendix D, (40), p.51

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_firstOrderThreshold
import Definitions.Def_KashUpgrade_jointTerm

namespace KashUpgrade

/-- **The first-order threshold maximizes the joint term.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (18)/(20), p.17 and Appendix D, (40),
p.51: for a block with positive total weight, `θ^{FOC}_B = v⁻¹(c ∑A / ∑A Δ)` lies in the support
and maximizes the joint term over the support.

**Formalization Note** The block `B` is any finite set of indices, which contains every block
`L'(i)`. -/
theorem appendixD_foc_maximizer {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {c : ℝ} (hc : 0 < c) (s : ℕ → ℕ) (A : ℕ → ℝ) (B : Finset ℕ) (hA : ∀ ℓ ∈ B, 0 ≤ A ℓ ∧ (0 < A ℓ → s (ℓ - 1) < s ℓ)) (hB : 0 < ∑ ℓ ∈ B, A ℓ) : firstOrderThreshold f ζ c s A B ∈ typeSupport ζ ∧ IsMaxOn (jointTerm f c s A B) (typeSupport ζ) (firstOrderThreshold f ζ c s A B) := by sorry

end KashUpgrade
