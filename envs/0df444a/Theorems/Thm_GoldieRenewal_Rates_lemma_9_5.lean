-- Prove2me | Theorems.Thm_GoldieRenewal_Rates_lemma_9_5
-- name    : GoldieRenewal.Rates.lemma_9_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:11:33.173873+00:00
-- url     : https://prove2.me/theorems/22ff3ba6-bd57-400e-8bbc-8777d47905f2
-- title:
--   Lemma 9.5 — Stone's inversion formula for the density of Σ χ ∗ μ^{(n)}
-- statement:
--   Let $\chi$ and $\mu$ be probability measures on $\mathbb R$. Suppose $\chi$ is absolutely continuous with density $q$ of class $C^2$ and compact support. Suppose $\int x^2\,\mu(dx)<\infty$, $m:=\int x\,\mu(dx)>0$, and that $\mu$ has an absolutely continuous component. Then the measure $\sum_{n\ge0}\chi*\mu^{(n)}$ is absolutely continuous with a continuous density $p$ satisfying, for every $x\in\mathbb R$,
--   $$p(x)-\frac1m\,\chi(-\infty,x]=\frac1{2\pi}\int_{\mathbb R}e^{-ix\theta}\,\hat\chi(\theta)\Big(\frac1{1-\hat\mu(\theta)}-\frac1{-im\theta}\Big)\,d\theta .$$
--
--   Here $\hat\chi(\theta)=\int e^{i\theta t}\chi(dt)$. The formula inverts the renewal density of a delayed renewal process and is the starting point of the explicit-rate Stone decomposition (Theorem 3.1).
--
--   **Formalization Note** The compact support of $q$ is an added hypothesis: the paper's proof uses $\hat\chi\in L^1(\mathbb R)$, which $q\in C^2$ alone does not give, and the lemma's only application has $q$ of class $C^2$ with compact support. "Has an absolutely continuous component" is "is not singular with respect to Lebesgue measure". At $\theta=0$ the integrand takes a junk value from division by zero; that point is Lebesgue-null.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, pp. 149–150, Lemma 9.5

import Mathlib
import Definitions.Def_QueueingFundamentals_MG1_transforms
import Definitions.Def_GoldieRenewal_Rates_Transforms

open MeasureTheory Complex
open QueueingFundamentals.MG1 (convPow)

namespace GoldieRenewal.Rates

/-- **Lemma 9.5** (Goldie 1991, pp. 149–150; Stone's inversion formula). Let `χ` and `μ` be
probability measures on `ℝ`, `χ` absolutely continuous with density `q ∈ C²`; suppose
`∫ x² μ(dx) < ∞`, `m := ∫ x μ(dx) > 0` and that `μ` has an absolutely continuous component.
Then `Σ_{n≥0} χ ∗ μ^{(n)}` is absolutely continuous with a continuous density `p` satisfying
`p(x) − (1/m) χ(−∞, x] = (1/2π) ∫_ℝ e^{−ixθ} χ̂(θ) (1/(1 − μ̂(θ)) − 1/(−imθ)) dθ` for all `x`.
Formalization Note: the hypothesis that `q` has compact support is **added**: the proof uses
`χ̂ ∈ L¹(ℝ)` (p. 150), which `q ∈ C²` alone does not give, and the lemma's only use (proof of
Theorem 3.1, p. 151) has `q` of class `C²` with compact support. "μ has an absolutely
continuous component" is `¬ (μ ⟂ₘ Lebesgue)`. At `θ = 0` the integrand takes Lean's junk value
(division by zero); this single point is Lebesgue-null. -/
theorem lemma_9_5 (χ μ : Measure ℝ) [IsProbabilityMeasure χ] [IsProbabilityMeasure μ]
    (q : ℝ → ℝ) (hq_nonneg : ∀ x, 0 ≤ q x) (hq_smooth : ContDiff ℝ 2 q)
    (hq_supp : HasCompactSupport q)
    (hχ : χ = volume.withDensity (fun x => ENNReal.ofReal (q x)))
    (h_second : Integrable (fun x : ℝ => x ^ 2) μ)
    (h_mean : 0 < ∫ x, x ∂μ)
    (h_ac : ¬ (μ ⟂ₘ volume)) :
    ∃ p : ℝ → ℝ, Continuous p ∧ (∀ x, 0 ≤ p x) ∧
      Measure.sum (fun n => Measure.conv χ (convPow μ n)) =
        volume.withDensity (fun x => ENNReal.ofReal (p x)) ∧
      ∀ x : ℝ,
        (p x : ℂ) - ((1 / (∫ y, y ∂μ)) * χ.real (Set.Iic x) : ℝ) =
          (1 / (2 * Real.pi : ℂ)) *
            ∫ θ : ℝ, Complex.exp (-(I * (x : ℂ) * (θ : ℂ))) * charTransform χ θ *
              (1 / (1 - charTransform μ θ) - 1 / (-(I * ((∫ y, y ∂μ : ℝ) : ℂ) * (θ : ℂ)))) := by sorry

end GoldieRenewal.Rates
