-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:21.510829+00:00
-- url     : https://prove2.me/theorems/6ef0164c-f2a7-4cf0-81c8-23be29e9ee22
-- title:
--   Grouped Cumulant Expansion for Inverse Covariance
-- statement:
--   This formalizes the grouped expansion in Equations (72)–(74) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), cited for the spatial step of Lemma 4.3.
--
--   Let $\mu$ be a compactly supported probability measure on a finite-dimensional real inner-product space $E$. Assume the covariance operator $A=\operatorname{Cov}(\mu)$ is invertible. For $m\ge3$, directions $h:\operatorname{Fin}(m)\to E$, and a fixed index $i_0\in\operatorname{Fin}(m)$, define $v(z)=\nabla\Lambda_\mu(z)-\nabla\Lambda_\mu(0)$. Then
--
--   $$D^m\langle v,A^{-1}v\rangle(0)[h]
--   =2m\,\kappa_m(h)+2\sum_{q:\,q(i_0)=\mathrm{true}\atop 2\le |q|\le m-2,\ 2\le |\neg q|\le m-2}
--   \left\langle\kappa_{|q|+1}(h_q,\cdot),A^{-1}\kappa_{m-|q|+1}(h_{\neg q},\cdot)\right\rangle.$$
--
--   The singleton and complementary-singleton allocations contribute $2m\,\kappa_m(h)$, while the remaining allocations are paired by complementation. This is a deterministic fixed-measure identity, not a stochastic evolution statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact
--       (mu : ProbabilityMeasure E)
--       (hc : IsCompact (mu : Measure E).support)
--       (hA : IsUnit (Covariance.operator (mu : Measure E)))
--       {m : ℕ} (hm : 3 ≤ m) (h : Fin m → E) (i0 : Fin m) :
--       iteratedFDeriv ℝ m (fun z : E =>
--           ⟪gradient (logLaplace (mu : Measure E)) z - gradient (logLaplace (mu : Measure E)) 0,
--             Ring.inverse (Covariance.operator (mu : Measure E))
--               (gradient (logLaplace (mu : Measure E)) z -
--                 gradient (logLaplace (mu : Measure E)) 0)⟫) 0 h =
--         (2 * (m : ℝ)) * cumulant (mu : Measure E) m h +
--           2 * ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
--             q i0 = true ∧
--             2 ≤ (selected h q).length ∧
--             2 ≤ (selected h (fun i => !(q i))).length),
--             ⟪cumulantVector (mu : Measure E) (selected h q),
--               Ring.inverse (Covariance.operator (mu : Measure E))
--                 (cumulantVector (mu : Measure E)
--                   (selected h (fun i => !(q i))))⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Cumulant/Leibniz`](https://prove2.me/theorems/dc69b9b3-3173-4efb-aee3-b6d1282be46f).
--
--   Definition modules: [`Analysis/BakryEmery/Cumulant/Basic`](https://prove2.me/theorems/c2d5b99d-f2d1-47d4-a2c5-2cf685ca2598), [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Analysis/BakryEmery/Cumulant/Local`](https://prove2.me/theorems/7a0cd01c-3ad0-460b-af3d-e088447d401d), [`Analysis/IteratedDerivative/Bilinear`](https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229).
--
--   Supporting theorems: [`inner_cumulantVector_single_ringInverse_cumulantVector`](https://prove2.me/theorems/9237a40c-7f1f-4233-8865-0d20c1925f94), [`iteratedFDeriv_inner_centeredGradient_zero_of_compact`](https://prove2.me/theorems/51587601-8a8b-458d-95cb-37b7054bab4d), [`selected_mask_partition`](https://prove2.me/theorems/cf1a6d5b-9b6d-481c-ae20-5dfef1453e3e), [`sum_filter_eq_two_mul_sum_filter_of_compl_invariant`](https://prove2.me/theorems/df0e8f70-61ce-476e-a922-0def8bd9c052).
--
--   Previous: [`iteratedFDeriv_inner_centeredGradient_zero_of_compact`](https://prove2.me/theorems/51587601-8a8b-458d-95cb-37b7054bab4d).
--
--   [Source excerpt, lines 153–171](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L153-L171) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 4.3, p. 20; Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equations (72) and (74), pp. 20–21 (spatial step of the proof of Lemma 4.3). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Cumulant/Leibniz.lean#L148-L465 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Cumulant.Leibniz`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Leibniz

open MeasureTheory
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact_readable
    (mu : ProbabilityMeasure E)
    (hc : IsCompact (mu : Measure E).support)
    (hA : IsUnit (Covariance.operator (mu : Measure E)))
    {m : ℕ} (hm : 3 ≤ m) (h : Fin m → E) (i0 : Fin m) :
    iteratedFDeriv ℝ m (fun z : E =>
        ⟪gradient (logLaplace (mu : Measure E)) z - gradient (logLaplace (mu : Measure E)) 0,
          Ring.inverse (Covariance.operator (mu : Measure E))
            (gradient (logLaplace (mu : Measure E)) z -
              gradient (logLaplace (mu : Measure E)) 0)⟫) 0 h =
      (2 * (m : ℝ)) * cumulant (mu : Measure E) m h +
        2 * ∑ q ∈ Finset.univ.filter (fun q : Fin m → Bool =>
          q i0 = true ∧
          2 ≤ (selected h q).length ∧
          2 ≤ (selected h (fun i => !(q i))).length),
          ⟪cumulantVector (mu : Measure E) (selected h q),
            Ring.inverse (Covariance.operator (mu : Measure E))
              (cumulantVector (mu : Measure E)
                (selected h (fun i => !(q i))))⟫ := by sorry
