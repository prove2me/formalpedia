-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_isEldanCutoff_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.exists_isEldanCutoff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:34.498071+00:00
-- url     : https://prove2.me/theorems/c19ca091-9b2b-4723-a463-2678e5d1f088
-- title:
--   Existence Of The Cutoff Eldan Localization Process
-- statement:
--   This formalizes the existence assertion associated with Equation (67) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), locator Equation (67), p. 19. Let $\mu$ be a probability measure on $\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}(n))$ with compact support and assume that $\mu$ is isotropic. Let $W$ be an $n$-dimensional Brownian motion on a probability space $(\Omega,P)$, and let $\mathcal F$ be a right-continuous filtration satisfying the stated ordering and null-set hypotheses. For a cutoff function $\gamma$ satisfying `IsCutoff γ`, there exists a parameter process $p:\mathbb R\to\Omega\to\operatorname{Param}(n)$ satisfying `IsEldanCutoff μ hc W ℱ hW γ p`:
--
--   $$\exists p,\quad \operatorname{IsEldanCutoff}(\mu,h_c,W,\mathcal F,h_W,\gamma,p).$$
--
--   The predicate records the cutoff localization dynamics, including the initial parameter and the associated process properties. The theorem is the existence component of the cutoff-stage construction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_isEldanCutoff (hiso : KLS.Isotropic μ)
--       {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
--       (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       [ℱ.IsRightContinuous] (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
--       (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
--       (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
--       {γ : Param n → ℝ} (hγ : IsCutoff γ) :
--       ∃ p : ℝ → Ω → Param n, IsEldanCutoff μ hc W ℱ hW γ p
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/Process/Basic`](https://prove2.me/theorems/e451f491-3413-45b6-83f9-6d32bb29f918).
--
--   Definition modules: [`KLS/BKL/Localization/Coefficients`](https://prove2.me/theorems/d4044301-d978-4415-85b5-191b3ecf6f74), [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Brownian/Multidim`](https://prove2.me/theorems/e25335d2-7bb4-48bc-88b0-e5f06cc2eee3), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02).
--
--   Supporting theorems: [`cutoffCoefficients_admissible`](https://prove2.me/theorems/b3c27db8-2231-4fb1-9cdc-cc4964163df3), [`exists_isDiffusion`](https://prove2.me/theorems/7af98979-05ab-4014-86ce-c2315b88e573).
--
--   Next: [`IsEldanCutoff.continuous`](https://prove2.me/theorems/3156d5a3-dbca-44fb-850e-0592de8c55d8).
--
--   [Source excerpt, lines 44–51](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L44-L51) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (67), p. 19 (unnumbered display) and the compact stage before it. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/Process/Basic.lean#L42-L137 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.Process.Basic`, declaration `FunctionalInequalities.KLS.BKL.Localization.exists_isEldanCutoff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_Process_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open LevyStochCalc LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito
variable {n : ℕ} (μ : MeasureTheory.ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
  (hc : IsCompact (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).support)

theorem FunctionalInequalities.KLS.BKL.Localization.exists_isEldanCutoff_readable (hiso : KLS.Isotropic μ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : MultidimBrownianMotion P n) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    [ℱ.IsRightContinuous] (hW : ∀ k, IsBrownianFiltration (W.W k) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {γ : Param n → ℝ} (hγ : IsCutoff γ) :
    ∃ p : ℝ → Ω → Param n, IsEldanCutoff μ hc W ℱ hW γ p := by sorry
