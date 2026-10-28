-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_limsup_enorm_gradient_mollify_le_readable
-- name    : FunctionalInequalities.Energy.limsup_enorm_gradient_mollify_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:52.32985+00:00
-- url     : https://prove2.me/theorems/b7115fba-b7b4-4e77-ad68-d8e10c4a65ff
-- title:
--   Pointwise Limsup Bound for Mollified Gradients
-- statement:
--   This statement bounds the limiting gradient size of mollifications by the asymptotic Lipschitz constant.
--
--   Let $V$ be a finite-dimensional real inner-product space with complete Borel measurable structure, and let $m$ be an additive Haar measure. Let $g:V\to\mathbb R$ be continuous, and fix $x\in V$. For the prescribed sequence of positive mollification radii `radius j`, write `mollify m (radius j) g` for the corresponding mollifications. The gradient norm is regarded as an $[0,\infty]$-valued `ENNReal` quantity.
--
--   The limsup along $j\to\infty$ satisfies
--
--   $$
--   \limsup_{j\to\infty}
--   \left\|\nabla\bigl(\operatorname{mollify}(m,\operatorname{radius}(j),g)\bigr)(x)\right\|_{\!e}
--   \leq \operatorname{AsymptoticLipschitz.apply}(g,x).
--   $$
--
--   This is a pointwise technical estimate used in smooth recovery of asymptotic-Lipschitz energies. It is stated in `ENNReal`, so infinite values are allowed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem limsup_enorm_gradient_mollify_le (m : Measure V) [m.IsAddHaarMeasure]
--       {g : V → ℝ} (hg : Continuous g) (x : V) :
--       limsup (fun j ↦ ‖gradient (mollify m (radius j) g) x‖ₑ) atTop ≤
--         AsymptoticLipschitz.apply g x
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Definition modules: [`Energy/Euclidean/LipschitzApproximation/Measurable`](https://prove2.me/theorems/4ca87026-e2cc-45b4-8e9e-f0a5bba71236), [`Energy/LocalSlope/Relaxation`](https://prove2.me/theorems/5763c613-ee60-472a-abfb-a2d2d79c15c8), [`Energy/Euclidean/LipschitzApproximation/Kernel`](https://prove2.me/theorems/d8350731-5ebe-4c22-a05d-d6b04921850a).
--
--   Supporting theorems: [`lipschitzOnWith_mollify_ball`](https://prove2.me/theorems/f6c8681b-1ff6-4044-8f83-791d558075e3).
--
--   Previous: [`lipschitzOnWith_mollify_ball`](https://prove2.me/theorems/f6c8681b-1ff6-4044-8f83-791d558075e3) · Next: [`relaxation_le_asymptoticLipschitz_of_lipschitzWith`](https://prove2.me/theorems/0c999886-ba48-46f7-9658-d121570cc5c9).
--
--   [Source excerpt, lines 509–512](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L509-L512) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L506-L544 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.limsup_enorm_gradient_mollify_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [SecondCountableTopology V]

theorem FunctionalInequalities.Energy.limsup_enorm_gradient_mollify_le_readable (m : Measure V) [m.IsAddHaarMeasure]
    {g : V → ℝ} (hg : Continuous g) (x : V) :
    limsup (fun j ↦ ‖gradient (mollify m (radius j) g) x‖ₑ) atTop ≤
      AsymptoticLipschitz.apply g x := by sorry
