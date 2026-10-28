-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_Q_posSemidef_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_Q_posSemidef_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:32.523206+00:00
-- url     : https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845
-- title:
--   Positive Semidefiniteness of the Q Component
-- statement:
--   This formalizes the positivity property of the localization parameter in Equation (67), p. 19 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1). Let $μ$ be isotropic with compact support, let $γ$ satisfy the cutoff assumptions, and let $p$ be an `IsEldanCutoff` process driven by a multidimensional Brownian motion with Brownian filtration.
--
--   For $P$-almost every $ω$, every $t≥0$, the operator $Q_t(ω)$ is self-adjoint and positive semidefinite:
--
--   $$Q_t(ω)=Q_t(ω)^*\quad\text{and}\quad 0≤\langle Q_t(ω)x,x\rangle\ \text{for every }x.$$
--
--   The declaration uses `IsSelfAdjoint` and the quadratic-form inequality directly. It is a structural consequence used to express positivity of the evolving localization covariance correction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.ae_Q_posSemidef (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
--       (h : IsEldanCutoff μ hc W ℱ hW γ p) :
--       ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
--         IsSelfAdjoint (p t ω).2 ∧ ∀ x, 0 ≤ ⟪(p t ω).2 x, x⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Supporting theorems: [`inner_self_pos_of_comp_eq_id`](https://prove2.me/theorems/cd7bd662-8102-4f8b-ace4-e8e741d6c4ea), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`IsEldanCutoff.ae_inner_Q_eq_integral`](https://prove2.me/theorems/996b9078-50df-4528-8085-8b31a80e5f6a).
--
--   Previous: [`IsEldanCutoff.ae_inner_Q_eq_integral`](https://prove2.me/theorems/996b9078-50df-4528-8085-8b31a80e5f6a).
--
--   [Source excerpt, lines 429–432](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L429-L432) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L427-L472 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_Q_posSemidef`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic

open scoped NNReal ENNReal RealInnerProductSpace
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_Q_posSemidef_readable (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsSelfAdjoint (p t ω).2 ∧ ∀ x, 0 ≤ ⟪(p t ω).2 x, x⟫ := by sorry
