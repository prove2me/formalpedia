-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_exists_weighted_energy_le_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:14.379187+00:00
-- url     : https://prove2.me/theorems/0093b479-64bc-4ff4-8d31-2c2c61eec957
-- title:
--   A Time with Controlled Weighted Cumulant Energy
-- statement:
--   This formalizes an interval-averaging component related to the cumulant bounds cited as Theorem 4.1, p. 18, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be isotropic with compact support, let $p_t$ be an `IsEldanCutoff` process with cutoff $\gamma$, and fix $d\in\mathbb N$ and $u\in\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$. Assume:
--
--   1. $C\geq 0$.
--   2. For every parameter $q=(c,Q)$ with $Q$ self-adjoint and positive semidefinite, the cumulant energy $E_d(q)$ is at most $C$.
--   3. The map $q\mapsto E_d(q)$ is continuous.
--   4. $T_0>0$.
--
--   Then there is $t\in[T_0,2T_0]$ such that
--
--   $$
--   \int_\Omega \gamma(p_t(\omega))^2 E_d(p_t(\omega))\,dP(\omega)
--   \leq
--   \frac{I_d(2T_0)}{T_0},
--   $$
--
--   where $I_d(2T_0)$ is the `weightedEnergyIntegral` up to time $2T_0$.
--
--   This provides a finite-horizon replacement for selecting a subsequence with horizon tending to infinity.
--
--   **Formalization Note.** The cumulant energy is evaluated using `compactPosterior`; the displayed quantities are real-valued integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.exists_weighted_energy_le (hiso : KLS.Isotropic μ) {γ : Param n → ℝ} (hγ : IsCutoff γ)
--       (h : IsEldanCutoff μ hc W ℱ hW γ p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
--       {C : ℝ} (hC0 : 0 ≤ C)
--       (hC : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
--         cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C)
--       (hcont : Continuous fun q : Param n =>
--         cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
--       {T₀ : ℝ} (hT₀ : 0 < T₀) :
--       ∃ t ∈ Set.Icc T₀ (2 * T₀),
--         (∫ w, γ (p t w) ^ 2 *
--           cumulantEnergy (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P) ≤
--           weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/CutoffEnergy/Boundary`](https://prove2.me/theorems/fc1e6296-7365-450f-8b02-bedf52fdeb49).
--
--   Definition modules: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b).
--
--   Supporting theorems: [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845), [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8), [`IsEldanCutoff.integrable_integral_of_ae_bound`](https://prove2.me/theorems/00d79fdf-b844-4072-9e3f-f54285d97844), [`exists_le_setIntegral_div`](https://prove2.me/theorems/5ce5f2ed-8559-4220-9d87-a84f56353c15).
--
--   Previous: [`IsEldanCutoff.integral_energy_le_weighted_add`](https://prove2.me/theorems/c81a7719-fcaa-451a-93ca-ddc74bf08eb5).
--
--   [Source excerpt, lines 225–236](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean#L225-L236) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/CutoffEnergy/Boundary.lean#L222-L366 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.CutoffEnergy.Boundary`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_CutoffEnergy_Boundary

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} {μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
  {hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support}
  {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.exists_weighted_energy_le_readable (hiso : KLS.Isotropic μ) {γ : Param n → ℝ} (hγ : IsCutoff γ)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) (d : ℕ) (u : EuclideanSpace ℝ (Fin n))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u ≤ C)
    (hcont : Continuous fun q : Param n =>
      cumulantEnergy (compactPosterior μ hc q.1 q.2 : Measure (EuclideanSpace ℝ (Fin n))) d u)
    {T₀ : ℝ} (hT₀ : 0 < T₀) :
    ∃ t ∈ Set.Icc T₀ (2 * T₀),
      (∫ w, γ (p t w) ^ 2 *
        cumulantEnergy (compactPosterior μ hc (p t w).1 (p t w).2 : Measure (EuclideanSpace ℝ (Fin n))) d u ∂P) ≤
        weightedEnergyIntegral μ hc P γ p d u (2 * T₀) / T₀ := by sorry
