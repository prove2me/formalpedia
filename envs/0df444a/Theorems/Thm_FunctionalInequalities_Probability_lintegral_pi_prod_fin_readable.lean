-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_lintegral_pi_prod_fin_readable
-- name    : FunctionalInequalities.Probability.lintegral_pi_prod_fin_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:52.368477+00:00
-- url     : https://prove2.me/theorems/dd8d5725-3056-4089-9664-4a524cef8983
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lintegral_pi_prod_fin
--       (μ : Measure E) [SigmaFinite μ] (k : ℕ) (g : Fin k → E → ENNReal)
--       (hg : ∀ i, Measurable (g i)) :
--       (∫⁻ x, ∏ i : Fin k, g i (x i) ∂(Measure.pi fun _ : Fin k => μ)) =
--         ∏ i : Fin k, ∫⁻ x, g i x ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef).
--
--   Next: [`pi_normalizedSum_moments`](https://prove2.me/theorems/b953108f-0212-45af-8dae-b7d86bea1cca).
--
--   [Source excerpt, lines 27–31](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Product.lean#L27-L31) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L26-L73 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.lintegral_pi_prod_fin`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

open MeasureTheory ProbabilityTheory Filter
variable {E : Type*}
variable [MeasurableSpace E]

theorem FunctionalInequalities.Probability.lintegral_pi_prod_fin_readable
    (μ : Measure E) [SigmaFinite μ] (k : ℕ) (g : Fin k → E → ENNReal)
    (hg : ∀ i, Measurable (g i)) :
    (∫⁻ x, ∏ i : Fin k, g i (x i) ∂(Measure.pi fun _ : Fin k => μ)) =
      ∏ i : Fin k, ∫⁻ x, g i x ∂μ := by sorry
