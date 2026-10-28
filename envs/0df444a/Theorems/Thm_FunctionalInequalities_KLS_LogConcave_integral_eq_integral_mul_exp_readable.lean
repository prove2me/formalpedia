-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integral_eq_integral_mul_exp_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:02.521345+00:00
-- url     : https://prove2.me/theorems/e50ba0fe-194c-4fab-a951-2f7b7b282f0a
-- title:
--   Change Of Measure For A Tilted Haar Law
-- statement:
--   This theorem is the change-of-measure identity associated with a tilted Haar measure.
--
--   Let $V$ be a normed additive group with a measurable structure, let $m$ be an additive Haar measure, let $\nu$ be a probability measure, and let $U:V\to\mathbb R$. Assume
--
--   $$
--   \nu=m.\operatorname{tilted}(-U).
--   $$
--
--   Then, for every function $F:V\to\mathbb R$,
--
--   $$
--   \int_V F(x)\,dm(x)
--   =
--   \int_V Z e^{U(x)}F(x)\,d\nu(x),
--   \qquad
--   Z=\int_V e^{-U(y)}\,dm(y).
--   $$
--
--   The identity is stated without inner-product, finite-dimensional, or topological hypotheses beyond those required for the measures. It is a basic reusable formula for converting Haar integrals into integrals against the probability law; no integrability assumption on $F$ is separately imposed in the theorem.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_eq_integral_mul_exp (hνU : (ν : Measure V) = m.tilted (-U)) (F : V → ℝ) :
--       ∫ x, F x ∂m = ∫ x, ((∫ y, Real.exp (-U y) ∂m) * Real.exp (U x)) * F x ∂(ν : Measure V)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Kernel`](https://prove2.me/theorems/53a4cc1e-e3fe-4459-bbf4-e862b9c35c22).
--
--   Next: [`restrict_le_smul_of_eq_tilted`](https://prove2.me/theorems/7744a7a5-331d-4220-a88d-91325cd3a0c8).
--
--   [Source excerpt, lines 42–43](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L42-L43) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Kernel.lean#L38-L75 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Kernel`, declaration `FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Kernel

open MeasureTheory Filter Topology InnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] {U : V → ℝ}
omit [InnerProductSpace ℝ V] [BorelSpace V] [SecondCountableTopology V]
  [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.LogConcave.integral_eq_integral_mul_exp_readable (hνU : (ν : Measure V) = m.tilted (-U)) (F : V → ℝ) :
    ∫ x, F x ∂m = ∫ x, ((∫ y, Real.exp (-U y) ∂m) * Real.exp (U x)) * F x ∂(ν : Measure V) := by sorry
