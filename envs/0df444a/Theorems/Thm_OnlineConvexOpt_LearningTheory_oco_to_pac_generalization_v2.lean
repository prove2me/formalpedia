-- Prove2me | Theorems.Thm_OnlineConvexOpt_LearningTheory_oco_to_pac_generalization_v2
-- name    : OnlineConvexOpt.LearningTheory.oco_to_pac_generalization_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:22:27.468447+00:00
-- url     : https://prove2.me/theorems/f5ac0adb-09ad-4ff1-814c-08b272a7dcf6
-- title:
--   Theorem 9.5 — OCO regret implies agnostic PAC generalization (regret guarantee over convex bounded costs)
-- statement:
--   **Statement (Theorem 9.5).** Let $H$ be a convex hypothesis class in a real inner-product space, with affine predictors $h\mapsto\mathrm{pred}(h,x)$ (e.g. $h_w(x)=w^\top x$) and a loss $\ell(\hat y,y)\in[0,1]$ convex in the prediction. Let $A$ be a non-anticipating OCO algorithm over $H$ whose regret after $T$ iterations, against every sequence of cost functions convex on $H$ with values in $[0,1]$ on $H$, is guaranteed to be bounded by $\mathrm{Regret}_T(A)$. Run the reduction of Algorithm 29 on $T\ge1$ i.i.d. examples from $D$ and let $\bar h$ be its output and $h^\star=\arg\min_{h\in H}\mathrm{error}(h)$. Then for any $\delta\in(0,1]$, with probability at least $1-\delta$,
--   $$\mathrm{error}(\bar h)\le\mathrm{error}(h^\star)+\frac{\mathrm{Regret}_T(A)}{T}+\sqrt{\frac{8\log(2/\delta)}{T}} .$$
--
--   **Formalization Note.** The retired statement was *proved* without any learning theory: it granted $A$'s regret bound against *every* cost sequence and used `RegretT` with the junk-valued comparator `⨅ y ∈ H`, and those two together are satisfiable only when the parameter space is a single point. The new statement imports `OnlineConvexOpt_FirstOrder_Protocol_v2` (comparator the real infimum over $H$, genuine for $[0,1]$-valued costs on the nonempty $H$) and restricts the regret guarantee to the OCO setting the book works in — cost sequences convex on $H$ and bounded in $[0,1]$ there, the class to which the reduction's costs $f_t(h)=\ell(\mathrm{pred}(h,x_t),y_t)$ belong. The standing assumptions that make them belong to it and that the proof uses are explicit: $H$ convex (Algorithm 29's "convex hypothesis class"), $\ell$ convex in the prediction (its "convex loss function") and bounded in $[0,1]$ (§9.2.2), predictors affine in the hypothesis parameter (the book's linear $h_w(x)=w^\top x$), which also give $\mathrm{error}(\bar h)\le\frac1T\sum_t\mathrm{error}(h_t)$ by Jensen. Measurability of $\mathrm{pred}$, $\ell$, the iterates $h_t$ and $\bar h$ is the field's standing convention (the martingale argument needs the $h_t$ to be random variables). `IsOnlineAlgorithm` (non-anticipation, plays in $H$) and `IsAgnosticReductionRun` (Algorithm 29 with i.i.d. samples) are as before.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 158, Theorem 9.5 (PDF p. 180)

import Mathlib
import Definitions.Def_OnlineConvexOpt_LearningTheory_GeneralizationError
import Definitions.Def_OnlineConvexOpt_LearningTheory_AgnosticReduction
import Definitions.Def_OnlineConvexOpt_FirstOrder_Algorithm
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol_v2

open MeasureTheory

namespace OnlineConvexOpt.LearningTheory

/-- Theorem 9.5 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 158, PDF p. 180). Let `A` be an OCO algorithm over the convex hypothesis
class `H` whose regret after `T` iterations, against every sequence of convex `[0,1]`-valued
cost functions on `H`, is guaranteed to be bounded by `RegretT(A)`. Then, for the reduction of
Algorithm 29 run with a convex loss `ℓ` bounded in `[0,1]` and affine (e.g. linear,
`h_w(x) = w^⊤x`) predictors, for any `δ > 0`, with probability at least `1 − δ`,
`error(h̄) ≤ error(h⋆) + Regret_T(A)/T + √(8 log(2/δ)/T)`.

`h̄` is Algorithm 29's output (`IsAgnosticReductionRun`), `h⋆ = arg min_{h∈H}{error(h)}`
(p. 158). `hAnonant` requires `A` to be non-anticipating and to play inside `H`. Measurability
hypotheses (`hpred`, `hℓmeas`, `hhmeas`, `hhbar`) are the field's standing convention that all
the random variables in the proof's martingale argument are measurable.

Corrected version: the retired statement granted `A`'s regret bound against *every* cost
sequence (not only convex bounded ones), with the junk `⨅ y ∈ H` comparator; together these
were satisfiable only when `E` is a single point, which made the theorem provable without any
learning theory. `RegretT` is now the `OnlineConvexOpt_FirstOrder_Protocol_v2` regret (genuine
infimum over `H`, bounded below by `0` for `[0,1]`-valued costs), the regret guarantee is
restricted to the OCO setting the book works in (convex costs bounded in `[0,1]` on `H`, the
class to which the reduction's costs `f_t(h) = ℓ(h(x_t), y_t)` belong), and the standing
assumptions that `H` is convex, `ℓ` is convex in the prediction and the predictors are affine in
the hypothesis parameter (so that the reduction's costs are convex and `error(h̄) ≤
(1/T)∑error(h_t)` by Jensen) are made explicit. -/
theorem oco_to_pac_generalization_v2
    {X Y E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω} [IsProbabilityMeasure Prob]
    (D : Measure (X × Y)) [IsProbabilityMeasure D]
    (H : Set E) (hHconv : Convex ℝ H) (pred : E → X → ℝ) (ℓ : ℝ → Y → ℝ)
    (hℓbdd : ∀ yhat y, 0 ≤ ℓ yhat y ∧ ℓ yhat y ≤ 1)
    (hℓconv : ∀ y, ConvexOn ℝ Set.univ (fun yhat => ℓ yhat y))
    (hpredaff : ∀ (x : X) (h₁ h₂ : E) (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
      pred (a • h₁ + b • h₂) x = a * pred h₁ x + b * pred h₂ x)
    (hpred : Measurable (Function.uncurry pred))
    (hℓmeas : Measurable (Function.uncurry ℓ))
    (A : (ℕ → E → ℝ) → ℕ → E)
    (hAnonant : OnlineConvexOpt.FirstOrder.IsOnlineAlgorithm H A)
    (RegretBoundA : ℕ → ℝ)
    (hA : ∀ (T : ℕ) (f : ℕ → E → ℝ), 1 ≤ T →
      (∀ t, ConvexOn ℝ H (f t)) → (∀ t, ∀ x ∈ H, 0 ≤ f t x ∧ f t x ≤ 1) →
      OnlineConvexOpt.FirstOrder.RegretT H f (A f) T ≤ RegretBoundA T)
    (T : ℕ) (hT : 1 ≤ T)
    (samp : ℕ → Ω → X × Y) (h : ℕ → Ω → E) (hbar : Ω → E)
    (hrun : IsAgnosticReductionRun Prob D pred ℓ A T samp h hbar)
    (hhmeas : ∀ t, Measurable (h t)) (hhbar : Measurable hbar)
    (hstar : E) (hstar_mem : hstar ∈ H)
    (hstar_min : ∀ y ∈ H, GeneralizationError D pred ℓ hstar ≤ GeneralizationError D pred ℓ y)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 - δ) ≤
      (Prob {ω | GeneralizationError D pred ℓ (hbar ω) ≤
        GeneralizationError D pred ℓ hstar + RegretBoundA T / T +
          Real.sqrt (8 * Real.log (2 / δ) / T)}).toReal := by sorry

end OnlineConvexOpt.LearningTheory
