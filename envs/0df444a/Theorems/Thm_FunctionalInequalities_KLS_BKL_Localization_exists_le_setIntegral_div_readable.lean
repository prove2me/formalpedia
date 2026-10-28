-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_le_setIntegral_div_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.exists_le_setIntegral_div_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:41.883321+00:00
-- url     : https://prove2.me/theorems/5ce5f2ed-8559-4220-9d87-a84f56353c15
-- title:
--   Pointwise Bound by an Interval Average
-- statement:
--   This auxiliary lemma gives a mean-value bound for an integrable real function.
--
--   Let $T>0$ and let $f:\mathbb R\to\mathbb R$ be integrable on $(T,2T]$. Then there exists $t\in[T,2T]$ such that
--
--   $$
--   f(t)\leq \frac{1}{T}\int_{(T,2T]}f(s)\,ds.
--   $$
--
--   The lemma is a technical interval-averaging fact used to select a time with controlled energy.
--
--   **Formalization Note.** Integrability is required only for the restriction of $f$ to $(T,2T]$; the selected point lies in the closed interval $[T,2T]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem exists_le_setIntegral_div
--       {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
--       (hf : Integrable f (volume.restrict (Set.Ioc T (2 * T)))) :
--       ∃ t ∈ Set.Icc T (2 * T),
--         f t ≤ (∫ s in Set.Ioc T (2 * T), f s) / T
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CutoffEnergy/Boundary`](https://prove2.me/theorems/fc1e6296-7365-450f-8b02-bedf52fdeb49).
--
--   Next: [`IsEldanCutoff.integral_energy_le_weighted_add`](https://prove2.me/theorems/c81a7719-fcaa-451a-93ca-ddc74bf08eb5).
--
--   [Source excerpt, lines 76–80](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean#L76-L80) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean#L76-L123 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary`, declaration `_private.FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary.0.FunctionalInequalities.KLS.BKL.Localization.exists_le_setIntegral_div`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary

open MeasureTheory ProbabilityTheory Filter Topology

theorem FunctionalInequalities.KLS.BKL.Localization.exists_le_setIntegral_div_readable
    {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Integrable f (volume.restrict (Set.Ioc T (2 * T)))) :
    ∃ t ∈ Set.Icc T (2 * T),
      f t ≤ (∫ s in Set.Ioc T (2 * T), f s) / T := by sorry
