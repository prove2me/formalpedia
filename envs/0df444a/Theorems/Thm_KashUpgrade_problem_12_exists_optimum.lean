-- Prove2me | Theorems.Thm_KashUpgrade_problem_12_exists_optimum
-- name    : KashUpgrade.problem_12_exists_optimum
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:22:29.598474+00:00
-- url     : https://prove2.me/theorems/494fa1c1-5434-4a60-b4c3-a69eb558a1b6
-- title:
--   Implicit, p.18 and p.53 — problem (12) attains its maximum
-- statement:
--   Let the type law satisfy Assumption 2, with Myerson price $p^*$, and let $c>0$. Let the weights be nonnegative, with positive intervals at the indices of positive weight. Then problem (12) has an optimal solution.
--
--   The paper speaks of "an optimal lumping for optimization problem (12)" and does not prove that one exists. For $\zeta=\infty$ this needs the tail of $(1-F(\theta))\theta$ to vanish, which Assumption 2 provides.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: θ unconstrained except for the order in (12) → θ in the support [0, ζ]; reason: thresholds are types; a threshold above a finite ζ has 1−F = 0 and the term value of ζ
--   - generalization: the weights of (38) and the intervals of the schedule → arbitrary nonnegative weights, where an index of positive weight has a positive interval; reason: the proof uses no more; the weights of (38) are of this kind
--   - reading: an optimal lumping L* for optimization problem (12) → an optimal solution exists; reason: the source presupposes it
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Lemma 3, p.18; Appendix F, p.53

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_IsMyersonPrice
import Definitions.Def_KashUpgrade_IsOptimalThreshold

namespace KashUpgrade

/-- **Problem (12) attains its maximum.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), p.18 and Appendix F, p.53: the paper speaks of "an
optimal lumping for optimization problem (12)" without proving that an optimal solution exists.

**Formalization Note** The weights are nonnegative, and an index with positive weight has a positive
interval, which covers the weights of (38). -/
theorem problem_12_exists_optimum {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {p : ℝ} (hp : IsMyersonPrice f p) {c : ℝ} (hc : 0 < c) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ) (hA : ∀ ℓ ∈ Finset.Icc (j + 1) (j + n), 0 ≤ A ℓ ∧ (0 < A ℓ → s (ℓ - 1) < s ℓ)) : ∃ θ, IsOptimalThreshold f ζ p c s A j n θ := by sorry

end KashUpgrade
