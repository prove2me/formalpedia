-- Prove2me | Theorems.Thm_KashUpgrade_myerson_price_exists_unique
-- name    : KashUpgrade.myerson_price_exists_unique
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:21:52.552232+00:00
-- url     : https://prove2.me/theorems/9ae9a7f9-27a8-460a-a253-b4eb9299a145
-- title:
--   §4.1, p.13 — the Myerson price $p^*$ exists and is unique
-- statement:
--   Let the type law satisfy Assumption 2. Then the problem
--   $$
--   \arg\max_{\theta\ge 0}\,(1-F(\theta))\cdot\theta
--   $$
--   has exactly one solution.
--
--   The paper defines $p^*$ as this $\arg\max$ and uses it as a number from then on. This statement ensures that the hypothesis "$p$ is a Myerson price" of the later results is met by exactly one $p$ for every type law.
--
--   Differences from the source:
--   - reading: p* := argmax_{θ ≥ 0} (1−F(θ))θ, written as one number → the maximizer exists and is unique; reason: the source’s definition presupposes it
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), §4.1, p.13

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_IsMyersonPrice

namespace KashUpgrade

/-- **`p*` is well defined.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), §4.1, p.13: under Assumption 2 the problem
`argmax_{θ ≥ 0} (1 - F θ) · θ` has exactly one solution. The paper uses this without stating it.
-/
theorem myerson_price_exists_unique {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) : ∃! p, IsMyersonPrice f p := by sorry

end KashUpgrade
