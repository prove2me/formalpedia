-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_measure_norm_gt_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measure_norm_gt_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:28.100983+00:00
-- url     : https://prove2.me/theorems/132ae609-cd45-4dbe-ab0d-e0f6ebb6fda6
-- title:
--   Lyapunov-Based Tail Bound
-- statement:
--   This is a Markov-type tail estimate associated in the literature register with Theorem 4.1, p. 18, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be isotropic with compact support, let $p_t$ be an `IsEldanCutoff` process with ball cutoff, and assume:
--
--   1. The filtration and null-set compatibility hypotheses hold.
--   2. $K\geq0$ and the generator satisfies $\mathcal L\mathcal V(q)\leq K\mathcal V(q)$ for every self-adjoint positive-semidefinite parameter matrix.
--   3. $t\geq0$ and $R>0$.
--
--   Then
--
--   $$
--   P\big(\|p_t\|>R\big)_{\mathrm{toReal}}
--   \leq
--   \frac{\mathcal V(0)e^{Kt}}{R^2}.
--   $$
--
--   The result converts the Lyapunov moment estimate into a probability tail bound for the parameter process.
--
--   **Formalization Note.** The probability is an `ENNReal` measure converted with `toReal`; the denominator is the ordinary real number $R^2$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.measure_norm_gt_le (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (h : IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
--       (hK : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
--         generator μ hc (lyapunov μ hc) q ≤ K * lyapunov μ hc q)
--       {t : ℝ} (ht : 0 ≤ t) {R : ℝ} (hR : 0 < R) :
--       (P {ω | R < ‖p t ω‖}).toReal ≤ lyapunov μ hc 0 * Real.exp (K * t) / R ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Moment`](https://prove2.me/theorems/efd9f37b-5ca3-4919-b8ed-5afbf25b7a3c).
--
--   Definition modules: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7).
--
--   Supporting theorems: [`opNorm_sq_le_hsNormSq`](https://prove2.me/theorems/4e1eeade-d7a1-4e5a-8b0a-e8fcba8ae762), [`IsEldanCutoff.integral_lyapunov_le`](https://prove2.me/theorems/d9f68ec0-3a26-4968-8fa3-4c402bb735c1).
--
--   Previous: [`IsEldanCutoff.integral_lyapunov_le`](https://prove2.me/theorems/d9f68ec0-3a26-4968-8fa3-4c402bb735c1).
--
--   [Source excerpt, lines 309–316](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean#L309-L316) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean#L309-L359 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measure_norm_gt_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.measure_norm_gt_le_readable (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      generator μ hc (lyapunov μ hc) q ≤ K * lyapunov μ hc q)
    {t : ℝ} (ht : 0 ≤ t) {R : ℝ} (hR : 0 < R) :
    (P {ω | R < ‖p t ω‖}).toReal ≤ lyapunov μ hc 0 * Real.exp (K * t) / R ^ 2 := by sorry
