-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_ae_inner_Q_eq_integral_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_inner_Q_eq_integral_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:09:55.51329+00:00
-- url     : https://prove2.me/theorems/996b9078-50df-4528-8085-8b31a80e5f6a
-- title:
--   Pathwise Integral Formula for the Q Component
-- statement:
--   This formalizes the $Q$-component identity associated with Equation (67), p. 19 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), partially formalizing the localization posterior and parameter evolution. Let $μ$ be an isotropic probability measure on $\operatorname{EuclideanSpace}(ℝ,Fin\,n)$ with compact support, let $γ$ be an admissible cutoff, and let $p_t=(c_t,Q_t)$ be an `IsEldanCutoff` process driven by a multidimensional Brownian motion.
--
--   For $P$-almost every sample $ω$, every $t≥0$, and all $x,y∈\operatorname{EuclideanSpace}(ℝ,Fin\,n)$,
--
--   $$\langle Q_t(ω)x,y\rangle
--   =\int_{(0,t]}γ(p_s(ω))^2\,\langle\operatorname{cov}(μ_{p_s(ω)})^{-1}x,y\rangle\,ds.$$
--
--   In the Lean statement the covariance is represented by `cov μ hc`, its inverse by `Ring.inverse`, and the parameter space is `Param n`. The conclusion is almost sure but uniform over all times and vectors, and the integral is a Lebesgue integral over `Set.Ioc`.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.ae_inner_Q_eq_integral (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
--       (h : IsEldanCutoff μ hc W ℱ hW γ p) :
--       ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ x y : EuclideanSpace ℝ (Fin n),
--         ⟪(p t ω).2 x, y⟫ =
--           ∫ s in Set.Ioc (0 : ℝ) t, γ (p s ω) ^ 2 * ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Supporting theorems: [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`cutoffCoefficients_admissible`](https://prove2.me/theorems/b3c27db8-2231-4fb1-9cdc-cc4964163df3), [`IsDiffusion.ae_linear_eq_integral`](https://prove2.me/theorems/6d3adf9d-0e82-429c-930c-0f1ece93e1b1), [`contDiff_posteriorCovariance_joint`](https://prove2.me/theorems/a52d87ad-7224-4ad7-973f-f486c36649d8).
--
--   Previous: [`IsEldanCutoff.dynkin`](https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba) · Next: [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845).
--
--   [Source excerpt, lines 247–251](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L247-L251) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L245-L425 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_inner_Q_eq_integral`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic

open scoped NNReal ENNReal RealInnerProductSpace
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.ae_inner_Q_eq_integral_readable (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ x y : EuclideanSpace ℝ (Fin n),
      ⟪(p t ω).2 x, y⟫ =
        ∫ s in Set.Ioc (0 : ℝ) t, γ (p s ω) ^ 2 * ⟪Ring.inverse (cov μ hc (p s ω)) x, y⟫ := by sorry
