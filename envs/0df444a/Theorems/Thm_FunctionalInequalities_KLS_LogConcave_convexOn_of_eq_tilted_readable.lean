-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_convexOn_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.convexOn_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:23.077058+00:00
-- url     : https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc
-- title:
--   Convexity of a Continuous Tilt Potential
-- statement:
--   This statement shows that a continuous potential representing a log-concave tilted law is convex.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $m$ be an additive Haar measure, and let $\nu$ be a log-concave probability measure. Suppose
--
--   $$\nu=m\mathbin{.}\mathrm{tilted}(-U)$$
--
--   for a continuous function $U:V\to\mathbb R$. Then $U$ is convex on all of $V$:
--
--   $$\operatorname{ConvexOn}(\mathbb R,\mathbb R^n,U).$$
--
--   Equivalently, for all $x,y\in V$ and $a,b\ge0$ with $a+b=1$,
--
--   $$U(ax+by)\le aU(x)+bU(y).$$
--
--   The result supplies the convexity of the potential needed to obtain nonnegative curvature in the heat-model arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convexOn_of_eq_tilted (hν : LogConcave ν) (hνU : (ν : Measure V) = m.tilted (-U))
--       (hU : Continuous U) : ConvexOn ℝ Set.univ U
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`integrable_exp_neg_of_eq_tilted`](https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70), [`integral_exp_neg_pos_of_eq_tilted`](https://prove2.me/theorems/fb765bf9-81da-4922-b614-0b50e7223f1c), [`interior_support_nonempty_of_eq_tilted`](https://prove2.me/theorems/f9e547f0-9041-4fe6-9d08-ab4991b4217f).
--
--   Previous: [`interior_support_nonempty_of_eq_tilted`](https://prove2.me/theorems/f9e547f0-9041-4fe6-9d08-ab4991b4217f) · Next: [`logConcave_of_eq_regularClass`](https://prove2.me/theorems/a4ee60d4-3b28-491b-804e-e9c2455e28ed).
--
--   [Source excerpt, lines 180–181](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L180-L181) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L177-L222 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.convexOn_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
variable [SecondCountableTopology V] (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.convexOn_of_eq_tilted_readable (hν : LogConcave ν) (hνU : (ν : Measure V) = m.tilted (-U))
    (hU : Continuous U) : ConvexOn ℝ Set.univ U := by sorry
