-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_continuous_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.continuous_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:10:41.226918+00:00
-- url     : https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8
-- title:
--   Continuity of Cutoff Localization Paths
-- statement:
--   This statement establishes path continuity for an `IsEldanCutoff` process. Let $p:ℝ→Ω→\operatorname{Param}(n)$ satisfy the cutoff Eldan-process assumptions, including the associated Brownian motion and filtration. Then every sample path is continuous:
--
--   $$\forall ω∈Ω,\qquad t\mapsto p_t(ω)\text{ is continuous on }ℝ.$$
--
--   The conclusion is everywhere in $ω$, not merely almost surely. It provides the regularity needed for subsequent pathwise integral and localization arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.continuous (h : IsEldanCutoff μ hc W ℱ hW γ p) (ω : Ω) :
--       Continuous fun t => p t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Previous: [`exists_isEldanCutoff`](https://prove2.me/theorems/c19ca091-9b2b-4723-a463-2678e5d1f088) · Next: [`IsEldanCutoff.dynkin`](https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba).
--
--   [Source excerpt, lines 146–147](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L146-L147) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L145-L162 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.continuous`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic

variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.continuous_readable (h : IsEldanCutoff μ hc W ℱ hW γ p) (ω : Ω) :
    Continuous fun t => p t ω := by sorry
