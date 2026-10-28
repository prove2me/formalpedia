-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integrable_integral_of_ae_bound_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integrable_integral_of_ae_bound_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:31.042532+00:00
-- url     : https://prove2.me/theorems/00d79fdf-b844-4072-9e3f-f54285d97844
-- title:
--   Integrability of Bounded Time Integrals
-- statement:
--   This auxiliary statement establishes integrability of time integrals along a cutoff Eldan process.
--
--   Let $P$ be a probability measure on $\Omega$, let $p_t(\omega)$ be an `IsEldanCutoff` process, and let $\varphi$ be a continuous real-valued function on the parameter space. Suppose that for some $B\in\mathbb R$,
--
--   $$
--   |\varphi(p_s(\omega))|\leq B
--   $$
--
--   for $P$-almost every $\omega$, simultaneously for every $s\geq 0$. Then, for every $T\geq 0$, the random variable
--
--   $$
--   \omega\longmapsto\int_{(0,T]}\varphi(p_s(\omega))\,ds
--   $$
--
--   is $P$-integrable.
--
--   The result supplies a basic integrability tool for later time-integration and interchange arguments.
--
--   **Formalization Note.** The almost-everywhere bound is uniform over all nonnegative times, and the time integral is with respect to Lebesgue measure restricted to $(0,T]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.integrable_integral_of_ae_bound (h : IsEldanCutoff μ hc W ℱ hW γ p)
--       {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
--       (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
--       Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω)) P
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b).
--
--   Definition modules: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Supporting theorems: [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8).
--
--   Next: [`IsEldanCutoff.measurable_uncurry_path`](https://prove2.me/theorems/0f4d530c-7ed9-4c80-861d-0a7145d978ff).
--
--   [Source excerpt, lines 28–31](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean#L28-L31) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean#L26-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Integral`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integrable_integral_of_ae_bound`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral

open MeasureTheory ProbabilityTheory Filter Topology
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integrable_integral_of_ae_bound_readable (h : IsEldanCutoff μ hc W ℱ hW γ p)
    {φ : Param n → ℝ} (hφ : Continuous φ) {B : ℝ}
    (hB : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → |φ (p s ω)| ≤ B) {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => ∫ s in Set.Ioc (0 : ℝ) T, φ (p s ω)) P := by sorry
