-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_integral_lyapunov_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_lyapunov_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:00.348124+00:00
-- url     : https://prove2.me/theorems/d9f68ec0-3a26-4968-8fa3-4c402bb735c1
-- title:
--   Exponential Lyapunov Moment Bound
-- statement:
--   This is an auxiliary Grönwall-type estimate for the cutoff Eldan process; the literature register relates it to Theorem 4.1, p. 18, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be isotropic with compact support, let $p_t$ be an `IsEldanCutoff` process with cutoff $\gamma$, and assume:
--
--   1. The filtration and null-set compatibility conditions hold.
--   2. $K\geq0$.
--   3. For every parameter $q=(c,Q)$ with $Q$ self-adjoint and positive semidefinite,
--      $$
--      \operatorname{generator}(\mu,h_c,\mathcal V)(q)\leq K\mathcal V(q),
--      $$
--      where $\mathcal V=\operatorname{lyapunov}(\mu,h_c)$.
--   4. $t\geq0$.
--
--   Then $\mathcal V(p_t)$ is $P$-integrable and
--
--   $$
--   \int_\Omega \mathcal V(p_t(\omega))\,dP(\omega)
--   \leq
--   \mathcal V(0)e^{Kt}.
--   $$
--
--   This estimate is the moment bound used to control the localization process and its tails.
--
--   **Formalization Note.** The generator inequality is assumed only on self-adjoint positive-semidefinite matrix components; no universal bound on $K$ is asserted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.integral_lyapunov_le (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (h : IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
--       (hK : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
--         generator μ hc (lyapunov μ hc) q ≤ K * lyapunov μ hc q)
--       {t : ℝ} (ht : 0 ≤ t) :
--       Integrable (fun ω => lyapunov μ hc (p t ω)) P ∧
--         ∫ ω, lyapunov μ hc (p t ω) ∂P ≤ lyapunov μ hc 0 * Real.exp (K * t)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Lyapunov/Moment`](https://prove2.me/theorems/efd9f37b-5ca3-4919-b8ed-5afbf25b7a3c).
--
--   Definition modules: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`KLS/BKL/Localization/Lyapunov/Basic`](https://prove2.me/theorems/1ed793bf-4e2f-450b-b764-c2de2f762cf7).
--
--   Selected supporting theorems: [`le_mul_exp_of_le_add_integral`](https://prove2.me/theorems/a6bad570-f51c-4919-9c6a-567bf7f49ada), [`Covariance.inner_operator_self_pos_of_affineSupport_eq_top`](https://prove2.me/theorems/5af59f78-fcb6-4c1e-a63a-8d36d8da7f37), [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845), [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8), [`IsEldanCutoff.dynkin`](https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba).
--
--   Next: [`IsEldanCutoff.measure_norm_gt_le`](https://prove2.me/theorems/132ae609-cd45-4dbe-ab0d-e0f6ebb6fda6).
--
--   [Source excerpt, lines 70–78](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean#L70-L78) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Lyapunov/Moment.lean#L70-L307 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Lyapunov.Moment`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_lyapunov_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Lyapunov_Moment

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.integral_lyapunov_le_readable (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      generator μ hc (lyapunov μ hc) q ≤ K * lyapunov μ hc q)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω => lyapunov μ hc (p t ω)) P ∧
      ∫ ω, lyapunov μ hc (p t ω) ∂P ≤ lyapunov μ hc 0 * Real.exp (K * t) := by sorry
