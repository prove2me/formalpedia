-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_measurable_uncurry_path_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measurable_uncurry_path_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:33.42726+00:00
-- url     : https://prove2.me/theorems/0f4d530c-7ed9-4c80-861d-0a7145d978ff
-- title:
--   Joint Measurability of the Eldan Path
-- statement:
--   This auxiliary measurability theorem concerns an `IsEldanCutoff` process $p_t(\omega)$.
--
--   For the product space $\Omega\times\mathbb R$, the map
--
--   $$
--   (\omega,s)\longmapsto p_s(\omega)
--   $$
--
--   is measurable.
--
--   This fact supports product-measure integration and Fubini or Tonelli arguments involving time and sample variables.
--
--   **Formalization Note.** The Lean expression is `fun z : Ω × ℝ => p z.2 z.1`; the order of the product coordinates is $(\omega,s)$ after projection.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.measurable_uncurry_path (h : IsEldanCutoff μ hc W ℱ hW γ p) :
--       Measurable (fun z : Ω × ℝ => p z.2 z.1)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b).
--
--   Definition modules: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Previous: [`IsEldanCutoff.integrable_integral_of_ae_bound`](https://prove2.me/theorems/00d79fdf-b844-4072-9e3f-f54285d97844) · Next: [`ae_prod_restrict_Ioc_of_ae`](https://prove2.me/theorems/f0520ab1-bee3-4ad8-9069-b5cd932d9737).
--
--   [Source excerpt, lines 109–110](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean#L109-L110) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean#L108-L123 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Integral`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measurable_uncurry_path`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral

variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measurable_uncurry_path_readable (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    Measurable (fun z : Ω × ℝ => p z.2 z.1) := by sorry
