-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_ae_prod_restrict_Ioc_of_ae_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.ae_prod_restrict_Ioc_of_ae_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:33.478343+00:00
-- url     : https://prove2.me/theorems/f0520ab1-bee3-4ad8-9069-b5cd932d9737
-- title:
--   Transfer of Almost-Everywhere Time Statements
-- statement:
--   This auxiliary measure-theoretic lemma transfers an almost-everywhere statement to a product measure.
--
--   Let $P$ be a probability measure on $\Omega$ and let $Q(\omega,s)$ be a proposition. If
--
--   $$
--   \text{for }P\text{-almost every }\omega,\quad Q(\omega,s)\text{ holds for every }s\geq0,
--   $$
--
--   then, for every real $T$, $Q(\omega,s)$ holds for $(P\otimes\operatorname{Leb}|_{(0,T]})$-almost every $(\omega,s)$.
--
--   This provides the almost-everywhere transfer needed for product-space integration over time intervals.
--
--   **Formalization Note.** No assumption $T\geq0$ is required; if the restricted interval is empty, the conclusion is vacuous.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_prod_restrict_Ioc_of_ae
--       [IsProbabilityMeasure P]
--       {Q : Ω → ℝ → Prop}
--       (hQ : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → Q w s) (T : ℝ) :
--       ∀ᵐ z ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))), Q z.1 z.2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Integral`](https://prove2.me/theorems/9ab8e8fa-a0fa-495b-bcfd-0abe91eb151b).
--
--   Previous: [`IsEldanCutoff.measurable_uncurry_path`](https://prove2.me/theorems/0f4d530c-7ed9-4c80-861d-0a7145d978ff).
--
--   [Source excerpt, lines 128–132](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean#L128-L132) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Integral.lean#L125-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Integral`, declaration `FunctionalInequalities.KLS.BKL.Localization.ae_prod_restrict_Ioc_of_ae`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Integral

open MeasureTheory ProbabilityTheory Filter Topology
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
omit [IsProbabilityMeasure P]

theorem FunctionalInequalities.KLS.BKL.Localization.ae_prod_restrict_Ioc_of_ae_readable
    [IsProbabilityMeasure P]
    {Q : Ω → ℝ → Prop}
    (hQ : ∀ᵐ w ∂P, ∀ s : ℝ, 0 ≤ s → Q w s) (T : ℝ) :
    ∀ᵐ z ∂(P.prod (volume.restrict (Set.Ioc (0 : ℝ) T))), Q z.1 z.2 := by sorry
