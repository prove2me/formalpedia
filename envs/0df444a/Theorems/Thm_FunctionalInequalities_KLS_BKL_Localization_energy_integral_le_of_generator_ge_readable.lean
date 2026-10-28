-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_energy_integral_le_of_generator_ge_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.energy_integral_le_of_generator_ge_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:48.980176+00:00
-- url     : https://prove2.me/theorems/af9c5a0b-2263-46d2-882d-a46979ba6e41
-- title:
--   Integrated Energy Bound from a Generator Inequality
-- statement:
--   This formalizes the integrated drift estimate associated with Lemma 5.2 of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $\mu$ be compactly supported, isotropic, and log-concave on $\operatorname{EuclideanSpace}(\mathbb{R},\operatorname{Fin}n)$, with support contained in $\overline B(0,\rho)$ for $\rho\ge0$. Let $P$ be a probability measure on a measurable space $\Omega$, let $W$ and $\mathcal F$ satisfy the Brownian-filtration assumptions, let $\gamma$ be a cutoff, and let $p$ be an Eldan cutoff process. Assume:
--
--   1. The filtration is nondecreasing from time $0$ toward nonpositive times and null measurable sets satisfy the stated measurability condition.
--   2. The order $r$ satisfies $r\ge2$.
--   3. The coefficient sequence $b_j$ is nonnegative.
--   4. The pointwise generator lower bound `h51` and lower-drift bound `hL` hold for every symmetric positive semidefinite posterior parameter.
--
--   Then, for every $u$ and $T\ge0$, the initial energy plus half the weighted energy integral is bounded by the terminal expected energy, the order-dependent weighted energy term, and the lower-order cross terms:
--
--   $$
--   E_r(0)+\frac12 I_{r+1}(T)
--   \le \mathbb E[E_r(T)]
--   +17(r+1)^2 I_r(T)
--   +2\sum_{a=2}^{r-1}\binom{r}{a-1}\sqrt{b_{r-a+2}}
--   \sqrt{I_r(T)}\sqrt{I_a(T)}.
--   $$
--
--   Here the Lean statement uses the explicitly defined `cumulantEnergy`, `weightedEnergyIntegral`, `generator`, posterior `lowerDrift`, and the exact finite sums and indices displayed in its type. The result is an integrated localization inequality, not a standalone universal cumulant bound.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       {T : ℝ} (hT : 0 ≤ T) :
--       cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) r u +
--           (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P γ p (r + 1) u T ≤
--         (∫ w, cumulantEnergy (compactPosterior μ hc (p T w).1 (p T w).2 :
--           Measure (EuclideanSpace ℝ (Fin n))) r u ∂P) +
--           17 * ((r : ℝ) + 1) ^ 2 *
--             weightedEnergyIntegral μ hc P γ p r u T +
--           2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
--             ((r + 1 - 1).choose (a - 1) : ℝ) *
--             Real.sqrt (b (r + 1 - a + 1)) *
--             (Real.sqrt (weightedEnergyIntegral μ hc P γ p r u T) *
--               Real.sqrt (weightedEnergyIntegral μ hc P γ p a u T))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Energy/Integral`](https://prove2.me/theorems/f4a73439-9c30-4a80-a66d-ff72b684af83).
--
--   Definition modules: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086), [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533), [`Probability/Posterior/CompactDomain`](https://prove2.me/theorems/38dd017c-ecae-4018-a0fd-eec5fa1b0dda), [`KLS/BKL/Localization/CutoffEnergy/Basic`](https://prove2.me/theorems/ae36e8bc-b0be-4294-a7b1-adcba1129d2b).
--
--   Selected supporting theorems: [`IsEldanCutoff.ae_Q_posSemidef`](https://prove2.me/theorems/adbc9c5b-5b86-46cc-9924-be91f135d845), [`IsEldanCutoff.dynkin`](https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba), [`IsEldanCutoff.measurable_uncurry_path`](https://prove2.me/theorems/0f4d530c-7ed9-4c80-861d-0a7145d978ff), [`ae_prod_restrict_Ioc_of_ae`](https://prove2.me/theorems/f0520ab1-bee3-4ad8-9069-b5cd932d9737), [`contDiff_cumulantEnergy_posterior`](https://prove2.me/theorems/0b698a15-4131-4b73-a00b-6eecdff79aa2).
--
--   [Source excerpt, lines 71–82](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Integral.lean#L71-L82) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 5.2, p. 24. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Energy/Integral.lean#L34-L383 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Energy.Integral`, declaration `FunctionalInequalities.KLS.BKL.Localization.energy_integral_le_of_generator_ge`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Energy_Integral

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace ContDiff
open FunctionalInequalities.Probability.Posterior FunctionalInequalities.Analysis
  FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Probability.Diffusion
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.KLS.BKL.Localization.energy_integral_le_of_generator_ge_readable (hiso : KLS.Isotropic μ) (hLC : KLS.LogConcave μ)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hsupp : (μ : Measure (EuclideanSpace ℝ (Fin n))).support ⊆ Metric.closedBall 0 ρ)
    (hγ : IsCutoff γ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {r : ℕ} (hr : 2 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h51 : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      (1 / 2 : ℝ) * cumulantEnergy (compactPosterior μ hc q.1 q.2 :
        Measure (EuclideanSpace ℝ (Fin n))) (r + 1) u -
        17 * ((r : ℝ) + 1) ^ 2 * cumulantEnergy
          (compactPosterior μ hc q.1 q.2 :
            Measure (EuclideanSpace ℝ (Fin n))) r u -
        2 * ∑ K : Fin r → Fin n,
          cumulant (compactPosterior μ hc q.1 q.2 :
            Measure (EuclideanSpace ℝ (Fin n))) (r + 1)
            (Fin.cons u fun s => inverseSqrt (cov μ hc q)
              (EuclideanSpace.basisFun (Fin n) ℝ (K s))) *
          lowerDrift (compactPosterior μ hc q.1 q.2 :
            Measure (EuclideanSpace ℝ (Fin n)))
            (Fin.cons u fun s => inverseSqrt (cov μ hc q)
              (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ≤
      generator μ hc
        (fun q' : Param n => cumulantEnergy
          (compactPosterior μ hc q'.1 q'.2 :
            Measure (EuclideanSpace ℝ (Fin n))) r u) q)
    (hL : ∀ q : Param n, IsSelfAdjoint q.2 → (∀ x, 0 ≤ ⟪q.2 x, x⟫) →
      Real.sqrt (∑ K : Fin r → Fin n,
        lowerDrift (compactPosterior μ hc q.1 q.2 :
          Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun s => inverseSqrt (cov μ hc q)
            (EuclideanSpace.basisFun (Fin n) ℝ (K s))) 0 ^ 2) ≤
        ∑ a ∈ Finset.Icc 2 (r + 1 - 2), ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1) * cumulantEnergy
            (compactPosterior μ hc q.1 q.2 :
              Measure (EuclideanSpace ℝ (Fin n))) a u))
    {T : ℝ} (hT : 0 ≤ T) :
    cumulantEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) r u +
        (1 / 2 : ℝ) * weightedEnergyIntegral μ hc P γ p (r + 1) u T ≤
      (∫ w, cumulantEnergy (compactPosterior μ hc (p T w).1 (p T w).2 :
        Measure (EuclideanSpace ℝ (Fin n))) r u ∂P) +
        17 * ((r : ℝ) + 1) ^ 2 *
          weightedEnergyIntegral μ hc P γ p r u T +
        2 * ∑ a ∈ Finset.Icc 2 (r + 1 - 2),
          ((r + 1 - 1).choose (a - 1) : ℝ) *
          Real.sqrt (b (r + 1 - a + 1)) *
          (Real.sqrt (weightedEnergyIntegral μ hc P γ p r u T) *
            Real.sqrt (weightedEnergyIntegral μ hc P γ p a u T)) := by sorry
