-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_tiltAverage_neg_weightedLaplacian_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:38.285576+00:00
-- url     : https://prove2.me/theorems/2049b0ee-2e67-44f2-a194-81ea5ae5e577
-- title:
--   Tilted Generator Identity
-- statement:
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel measurable structure, and let $m$ be a measure that is an additive Haar measure. Let $V,f:E\to\mathbb R$ satisfy:
--
--   1. $V$ is $C^1$.
--   2. $f$ is $C^2$.
--   3. $f$ has compact support.
--
--   For every $z\in E$, with $\mu=m.\operatorname{tilted}(-V)$, one has
--
--   $$
--   F_{-\mathcal Lf}(z)=\left\langle z,F_{\nabla f}(z)\right\rangle,
--   $$
--
--   where $F_h=\operatorname{tiltAverage}(\mu,h)$ and
--
--   $$
--   \mathcal Lf=\Delta f-\langle\nabla V,\nabla f\rangle.
--   $$
--
--   This is the generator identity used to convert weighted-Laplacian terms into gradient terms in the Taylor-tensor argument.
--
--   **Formalization Note** The statement is total even when $e^{-V}$ is not $m$-integrable: in that case the tilted measure is the zero measure and both sides vanish. No probability-measure assumption is present.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem tiltAverage_neg_weightedLaplacian {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
--       (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
--       tiltAverage (m.tilted (-V)) (fun x => -weightedLaplacian V f x) z =
--         ⟪z, tiltAverage (m.tilted (-V)) (gradient f) z⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Definition modules: [`Analysis/BakryEmery/Laplacian`](https://prove2.me/theorems/6d4fe636-d4d6-41ad-8a90-95a5712d28e4).
--
--   Supporting theorems: [`expTilt_tilted`](https://prove2.me/theorems/b77ce921-0d7b-4b31-ac8b-28afb215f4d2), [`gradient_sub_inner`](https://prove2.me/theorems/6e39480b-596b-4064-876c-d786d322b2b9), [`integrable_gradient_expTilt`](https://prove2.me/theorems/4ce78d47-f6fb-43d4-9cf4-e4a847a5b302), [`weightedLaplacian_eq_zero_of_notMem_tsupport`](https://prove2.me/theorems/b381f334-820c-4611-a1c1-f11888c8bc19).
--
--   Previous: [`integrable_gradient_expTilt`](https://prove2.me/theorems/4ce78d47-f6fb-43d4-9cf4-e4a847a5b302).
--
--   [Source excerpt, lines 156–159](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L156-L159) · Frozen source `408915f`.
--
--   **Literature**
--
--   This formalizes Equation (48) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1), Equation (48), p. 14.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Equation (48), p. 14 (unnumbered). Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Basic.lean#L154-L240 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic`, declaration `FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic

open scoped RealInnerProductSpace ContDiff
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]

theorem FunctionalInequalities.Analysis.BakryEmery.tiltAverage_neg_weightedLaplacian_readable {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
    tiltAverage (m.tilted (-V)) (fun x => -weightedLaplacian V f x) z =
      ⟪z, tiltAverage (m.tilted (-V)) (gradient f) z⟫ := by sorry
