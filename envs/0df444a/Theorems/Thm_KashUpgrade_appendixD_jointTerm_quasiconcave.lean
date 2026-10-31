-- Prove2me | Theorems.Thm_KashUpgrade_appendixD_jointTerm_quasiconcave
-- name    : KashUpgrade.appendixD_jointTerm_quasiconcave
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:39.519506+00:00
-- url     : https://prove2.me/theorems/67497cfc-ffb1-45de-8269-2979195b1c2d
-- title:
--   Appendix D, (39), p.51 — the joint terms are quasiconcave
-- statement:
--   Let the type law satisfy Assumption 2 and let $c>0$. For every finite set of indices $B$, with nonnegative weights $A_\ell$ and positive intervals at the indices of positive weight, the joint term
--   $$
--   (1-F(\theta))\sum_{\ell\in B}A_\ell\bigl((s_\ell-s_{\ell-1})\theta-c\bigr)
--   $$
--   is quasiconcave in $\theta$ on the support.
--
--   Quasiconcavity is what makes the order constraints of problem (12) tractable: a term increases up to its first-order point and decreases after it.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - generalization: the block L(i) of a lumping → any finite set of indices B; reason: every block is such a set
--   - generalization: the weights of (38) and the intervals of the schedule → arbitrary nonnegative weights, where an index of positive weight has a positive interval; reason: the proof uses no more; the weights of (38) are of this kind
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Appendix D, (39), p.51

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_jointTerm

namespace KashUpgrade

/-- **The joint terms are quasiconcave.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Appendix D, (39), p.51: under Assumption 2, the joint
term `(1 - F θ) ∑_{ℓ∈B} A_ℓ ((s_ℓ - s_{ℓ-1}) θ - c)` is quasiconcave in `θ` on the support.

**Formalization Note** The block `B` is any finite set of indices, which contains every block
`L(i)`. Weights are nonnegative, and an index with positive weight has a positive interval. -/
theorem appendixD_jointTerm_quasiconcave {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {c : ℝ} (hc : 0 < c) (s : ℕ → ℕ) (A : ℕ → ℝ) (B : Finset ℕ) (hA : ∀ ℓ ∈ B, 0 ≤ A ℓ ∧ (0 < A ℓ → s (ℓ - 1) < s ℓ)) : QuasiconcaveOn ℝ (typeSupport ζ) (jointTerm f c s A B) := by sorry

end KashUpgrade
