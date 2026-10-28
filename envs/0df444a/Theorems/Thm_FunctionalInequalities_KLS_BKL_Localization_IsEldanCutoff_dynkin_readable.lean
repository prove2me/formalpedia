-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_IsEldanCutoff_dynkin_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.dynkin_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:20.310236+00:00
-- url     : https://prove2.me/theorems/4bc350bc-15db-49c9-826f-42946b8cb2ba
-- title:
--   Dynkin Identity for the Cutoff Eldan Process
-- statement:
--   This formalizes the Dynkin identity associated with Equation (67), p. 19, of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), at the compact-support cutoff stage.
--
--   Let $n\in\mathbb N$, let $\mu$ be an isotropic probability measure on $\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$ with compact support, and let $P$ be a probability measure on a measurable sample space $\Omega$. Let $W$ be an $n$-dimensional multidimensional Brownian motion whose coordinates are Brownian with respect to a filtration $\mathcal F$. Let $\gamma$ be a cutoff on the parameter space and let $p_t(\omega)$ be an `IsEldanCutoff` process. Assume:
--
--   1. The filtration is decreasing from time $0$ toward nonpositive times: $\mathcal F_0\leq\mathcal F_t$ whenever $t\leq 0$.
--   2. Every $P$-null measurable set is measurable with respect to $\mathcal F_0$.
--   3. The cutoff and process satisfy the stated cutoff Eldan process conditions.
--   4. $F$ is a $C^2$ function on the parameter space, and $T\geq 0$.
--
--   Then $F(p_T)$ is $P$-integrable and its expectation satisfies
--
--   $$
--   \int_\Omega F(p_T(\omega))\,dP(\omega)-F(0)
--   =
--   \int_\Omega\int_{(0,T]}\gamma(p_s(\omega))^2\,\operatorname{generator}(\mu,h_c,F)(p_s(\omega))\,ds\,dP(\omega).
--   $$
--
--   This is a reusable expectation identity for twice continuously differentiable observables of the cutoff localization process.
--
--   **Formalization Note.** The integrals are Lebesgue integrals over $(0,T]$ and $P$; the generator is the uncut `generator`, multiplied by the squared cutoff coefficient.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem IsEldanCutoff.dynkin (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       (h : IsEldanCutoff μ hc W ℱ hW γ p) {F : Param n → ℝ} (hF : ContDiff ℝ 2 F)
--       {T : ℝ} (hT : 0 ≤ T) :
--       Integrable (fun ω => F (p T ω)) P ∧
--         ∫ ω, F (p T ω) ∂P - F 0 =
--           ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 * generator μ hc F (p s ω) ∂volume ∂P
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3).
--
--   Supporting theorems: [`cutoffCoefficients_admissible`](https://prove2.me/theorems/b3c27db8-2231-4fb1-9cdc-cc4964163df3), [`IsDiffusion.dynkin_transport`](https://prove2.me/theorems/f6431279-4b25-42b2-b8ca-132fe14a47cf).
--
--   Previous: [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8) · Next: [`IsEldanCutoff.ae_inner_Q_eq_integral`](https://prove2.me/theorems/996b9078-50df-4528-8085-8b31a80e5f6a).
--
--   [Source excerpt, lines 180–187](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L180-L187) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L177-L217 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.dynkin`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic

open MeasureTheory ProbabilityTheory Filter Topology
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)
variable {μ hc} {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P n} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hW : ∀ k, LevyStochCalc.Brownian.IsBrownianFiltration (W.W k) ℱ} {γ : FunctionalInequalities.KLS.BKL.Localization.Param n → ℝ} {p : ℝ → Ω → FunctionalInequalities.KLS.BKL.Localization.Param n}

theorem FunctionalInequalities.KLS.BKL.Localization.IsEldanCutoff.dynkin_readable (hiso : KLS.Isotropic μ) (hγ : IsCutoff γ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h : IsEldanCutoff μ hc W ℱ hW γ p) {F : Param n → ℝ} (hF : ContDiff ℝ 2 F)
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun ω => F (p T ω)) P ∧
      ∫ ω, F (p T ω) ∂P - F 0 =
        ∫ ω, ∫ s in Set.Ioc (0 : ℝ) T, γ (p s ω) ^ 2 * generator μ hc F (p s ω) ∂volume ∂P := by sorry
