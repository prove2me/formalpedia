-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_lintegral_pi_prod_fin_408915f
-- name    : FunctionalInequalities.Probability.lintegral_pi_prod_fin_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:35:28.918523+00:00
-- url     : https://prove2.me/theorems/82c2f214-e65a-4425-a412-302f1f1ea7fd
-- title:
--   Finite Product Factorization Of Lower Integrals
-- statement:
--   This statement gives the finite-product factorization of a lower integral.
--
--   Let $E$ be a measurable space, let $\mu$ be a sigma-finite measure on $E$, let $k\in\mathbb N$, and let $g_i:E\to[0,\infty]$ be measurable for every $i\in\operatorname{Fin}k$. Then
--   $$\int_{E^{\operatorname{Fin}k}}\prod_i g_i(x_i)\,d\bigotimes_i\mu
--   =\prod_i\int_E g_i(x)\,d\mu(x).$$
--
--   This is the finite-coordinate independence identity used in product-measure and suspension moment calculations.
--
--   **Formalization Note.** The integrands and integrals take values in $[0,\infty]$, represented by `ENNReal`; the product measure is `Measure.pi`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L26-L73 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.lintegral_pi_prod_fin`; the repository is private at upload time).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.lintegral_pi_prod_fin_408915f
    (μ : Measure E) [SigmaFinite μ] (k : ℕ) (g : Fin k → E → ENNReal)
    (hg : ∀ i, Measurable (g i)) :
    (∫⁻ x, ∏ i : Fin k, g i (x i) ∂(Measure.pi fun _ : Fin k => μ)) =
      ∏ i : Fin k, ∫⁻ x, g i x ∂μ := by sorry
