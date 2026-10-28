-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_lipschitzOnWith_mollify_ball_readable
-- name    : FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:54.302986+00:00
-- url     : https://prove2.me/theorems/f6c8681b-1ff6-4044-8f83-791d558075e3
-- title:
--   Local Lipschitz Bound for Mollification on Balls
-- statement:
--   This statement gives the local Lipschitz stability of mollification under an additive Haar measure.
--
--   Let $V$ be a finite-dimensional real inner-product space with its Borel measurable structure, and let $m$ be an additive Haar measure on $V$. Let $R,\delta\in\mathbb R$ satisfy $0<R$. Let $c\in[0,\infty)$, let $g:V\to\mathbb R$ be continuous, and fix $x\in V$. Assume that $g$ is $c$-Lipschitz on the ball of radius $\delta+2R$ centered at $x$.
--
--   Then the mollification `mollify m R g` is $c$-Lipschitz on the ball of radius $\delta$ centered at $x$:
--
--   $$
--   \operatorname{LipschitzOnWith}(c,g,B(x,\delta+2R))
--   \;\Longrightarrow\;
--   \operatorname{LipschitzOnWith}(c,\operatorname{mollify}(m,R,g),B(x,\delta)).
--   $$
--
--   The result is a local recovery tool: the radius-$R$ mollifier requires control only on the enlarged ball of radius $\delta+2R$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem lipschitzOnWith_mollify_ball (m : Measure V) [m.IsAddHaarMeasure]
--       {R δ : ℝ} (hR : 0 < R) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
--       (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
--       LipschitzOnWith c (mollify m R g) (Metric.ball x δ)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/Euclidean/Slope/Recovery`](https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce).
--
--   Definition modules: [`Energy/Euclidean/LipschitzApproximation/Kernel`](https://prove2.me/theorems/d8350731-5ebe-4c22-a05d-d6b04921850a).
--
--   Previous: [`apply_mul_le`](https://prove2.me/theorems/bf9de844-4401-433d-8497-f00f6238df47) · Next: [`limsup_enorm_gradient_mollify_le`](https://prove2.me/theorems/b7115fba-b7b4-4e77-ad68-d8e10c4a65ff).
--
--   [Source excerpt, lines 462–465](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L462-L465) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L459-L493 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, declaration `FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery

open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
omit [CompleteSpace V] [SecondCountableTopology V]

theorem FunctionalInequalities.Energy.lipschitzOnWith_mollify_ball_readable (m : Measure V) [m.IsAddHaarMeasure]
    {R δ : ℝ} (hR : 0 < R) {c : ℝ≥0} {g : V → ℝ} (hg : Continuous g) (x : V)
    (h : LipschitzOnWith c g (Metric.ball x (δ + 2 * R))) :
    LipschitzOnWith c (mollify m R g) (Metric.ball x δ) := by sorry
