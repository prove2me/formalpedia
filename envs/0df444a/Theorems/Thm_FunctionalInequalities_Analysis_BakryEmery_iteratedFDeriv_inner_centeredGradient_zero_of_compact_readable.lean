-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_centeredGradient_zero_of_compact_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:10.299078+00:00
-- url     : https://prove2.me/theorems/51587601-8a8b-458d-95cb-37b7054bab4d
-- title:
--   Raw Cumulant Expansion of a Centered Gradient Quadratic Form
-- statement:
--   This formalizes the raw expansion underlying Equation (74) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited as part of the spatial step of Lemma 4.3.
--
--   Let $E$ be finite-dimensional, let $\mu$ be a probability measure on $E$ with compact support, let $M:E\to E$ be continuous linear, let $m\in\mathbb N$, and let $h:\operatorname{Fin}(m)\to E$. Define
--   $$v(z)=\nabla\Lambda_\mu(z)-\nabla\Lambda_\mu(0),$$
--   where $\Lambda_\mu=\operatorname{logLaplace}(\mu)$. Then
--
--   $$D^m\langle v(z),Mv(z)\rangle\big|_{z=0}[h]
--   =\sum_{q\,:\,\exists i,\ q(i)=\mathrm{true}\ \wedge\ \exists i,\ q(i)=\mathrm{false}}\left\langle \kappa_{|q|+1}(h_q,\cdot),M\kappa_{m-|q|+1}(h_{\neg q},\cdot)\right\rangle,$$
--
--   where `selected` forms the ordered sublists $h_q$ and $h_{\neg q}$, and the sum ranges over Boolean masks selecting both at least one direction and at least one complementary direction.
--
--   This is a deterministic raw Leibniz expansion; it contains no stochastic-process or cumulant-evolution assertion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_inner_centeredGradient_zero_of_compact (μ : ProbabilityMeasure E)
--       (hc : IsCompact (μ : Measure E).support) (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → E) :
--       iteratedFDeriv ℝ m (fun z : E =>
--           ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
--             M (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
--         ∑ q ∈ (Finset.univ.filter fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false)),
--           ⟪cumulantVector (μ : Measure E) (selected h q),
--             M (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Leibniz`](https://prove2.me/theorems/dc69b9b3-3173-4efb-aee3-b6d1282be46f).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d), [`Analysis/IteratedDerivative/Bilinear`](https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229).
--
--   Supporting theorems: [`directional_centeredGradient_logLaplace_zero_of_compact`](https://prove2.me/theorems/9f51014f-22c8-44a0-ab77-cef40f1a23ab), [`directional_bilinear`](https://prove2.me/theorems/c7268247-0081-4a71-b098-d28d94f91226).
--
--   Previous: [`directional_centeredGradient_logLaplace_zero_of_compact`](https://prove2.me/theorems/9f51014f-22c8-44a0-ab77-cef40f1a23ab) · Next: [`iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact`](https://prove2.me/theorems/6ef0164c-f2a7-4cf0-81c8-23be29e9ee22).
--
--   [Source excerpt, lines 61–68](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L61-L68) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18; Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equations (72) and (74), pp. 20–21 (spatial step of the proof of Lemma 4.3). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L60-L146 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Leibniz

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_of_compact_readable (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → E) :
    iteratedFDeriv ℝ m (fun z : E =>
        ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
          M (gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)⟫) 0 h =
      ∑ q ∈ (Finset.univ.filter fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false)),
        ⟪cumulantVector (μ : Measure E) (selected h q),
          M (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ := by sorry
