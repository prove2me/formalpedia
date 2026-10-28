-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_rpow_mul_rpow_le_of_convexOn_readable
-- name    : FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:15.043523+00:00
-- url     : https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5
-- title:
--   Log-Concavity of a Normalized Convex Potential Weight
-- statement:
--   This proves the pointwise log-concavity inequality for a normalized exponential weight.
--
--   Let $V$ be a real inner-product space, let $W:V\to\mathbb R$ be convex on all of $V$, and let $Z>0$. For $x,y\in V$ and $0<t<1$,
--
--   $$\left(\frac{e^{-W(x)}}{Z}\right)^t
--   \left(\frac{e^{-W(y)}}{Z}\right)^{1-t}
--   \le
--   \frac{e^{-W(tx+(1-t)y)}}{Z}.$$
--
--   The powers are real powers `Real.rpow`, and the positivity assumption on $Z$ is explicit. This is the density-level inequality used to show that exponential tilts by convex potentials are log-concave.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem rpow_mul_rpow_le_of_convexOn {W : V → ℝ} (hconv : ConvexOn ℝ Set.univ W) {Z : ℝ}
--       (hZ : 0 < Z) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
--       (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
--         Real.exp (-W (t • x + (1 - t) • y)) / Z
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Previous: [`integral_exp_neg_pos_of_eq_tilted`](https://prove2.me/theorems/fb765bf9-81da-4922-b614-0b50e7223f1c) · Next: [`isBorellDensity_of_eq_tilted`](https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de).
--
--   [Source excerpt, lines 77–80](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L77-L80) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L74-L117 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem FunctionalInequalities.KLS.LogConcave.rpow_mul_rpow_le_of_convexOn_readable {W : V → ℝ} (hconv : ConvexOn ℝ Set.univ W) {Z : ℝ}
    (hZ : 0 < Z) (x y : V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (Real.exp (-W x) / Z) ^ t * (Real.exp (-W y) / Z) ^ (1 - t) ≤
      Real.exp (-W (t • x + (1 - t) • y)) / Z := by sorry
