-- Prove2me | Theorems.Thm_LimitedPriceChanges_LowerBound_theorem_2
-- name    : LimitedPriceChanges.LowerBound.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:04:19.026066+00:00
-- url     : https://prove2.me/theorems/fad3f70c-4d8d-43ce-ba80-6a57d70fcbf4
-- title:
--   Theorem 2, p. 10 — minimax regret with at most m price changes
-- statement:
--   Fix an integer $m\ge1$. There are constants $K_7>0$ and $T_0$ depending only on $m$ such that, for every $T\ge T_0$ and every randomized admissible policy that changes price at most $m$ times, some parameter $z\in[1/6,5/6]$ in the Bernoulli instance forces
--   $$R_\pi(T,z)\ge K_7T^{1/(m+1)}.$$
--   Prices lie in $[1,6]$; demand has success probability $\max\{0,1-pz/2\}$; inventory is replenished to one, and holding and shortage costs are zero. The result gives the minimax rate matching the paper's upper-bound exponent.
--
--   **Formalization Note** Lean periods are zero-based and the budget holds for every seed and demand path. Randomization is represented by a probability seed and its expected regret by a nonnegative lintegral. The policy is quantified before the adversarial parameter. This is the minimax reading of (56); the theorem's literal “one instance for every algorithm” order is false because an algorithm knowing $z$ can always choose $1/z$. Naming the printed Bernoulli family strengthens the theorem's existential instance claim. This family violates the positive-mean and identifiability assumptions of §2–3 at prices beyond the zero-demand kink, as it does in the paper.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), p. 10, Theorem 2; p. 35, Bernoulli construction; p. 37, (56)

import Mathlib
import Definitions.Def_LimitedPriceChanges_LowerBound_Policy

namespace LimitedPriceChanges.LowerBound

/-- Theorem 2, p. 10, in the minimax order proved for the Bernoulli instance of p. 35. -/
theorem theorem_2 (m : ℕ) (hm : 1 ≤ m) :
    ∃ K7 : ℝ, 0 < K7 ∧ ∃ T0 : ℕ, ∀ T ≥ T0,
      ∀ (S : Type) [MeasurableSpace S] (μ : MeasureTheory.Measure S)
        [MeasureTheory.IsProbabilityMeasure μ] (π : Policy S T m),
        ∃ z ∈ Set.Icc (1 / 6 : ℝ) (5 / 6 : ℝ),
          ENNReal.ofReal (K7 * (T : ℝ) ^ ((1 : ℝ) / ((m : ℝ) + 1))) ≤
            regret μ π z := by sorry

end LimitedPriceChanges.LowerBound
