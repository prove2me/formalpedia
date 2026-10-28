-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_relaxation_eq_intrinsic_energy_readable
-- name    : FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:49.863509+00:00
-- url     : https://prove2.me/theorems/173a210b-c07a-4836-9df1-d0ac82ab944a
-- title:
--   Ambient–Intrinsic Relaxation Energy Equality
-- statement:
--   This theorem identifies the ambient and intrinsic smooth-gradient relaxation energies for a finite-dimensional probability measure.
--
--   Let $E$ be a finite-dimensional real inner-product space that is a normed additive commutative group, complete, equipped with a measurable structure and its Borel structure, and having a second-countable topology. Let $\mu$ be a probability measure on $E$.
--
--   The two extended-valued energies, namely `SmoothGradient.relaxation μ` and `SmoothGradient.Intrinsic.energy μ`, are equal as functionals on the common original $L^2(\mu)$ space:
--
--   $$
--   \operatorname{relaxation}(\mu)=\operatorname{Intrinsic.energy}(\mu).
--   $$
--
--   The equality includes the possibility that either energy takes the value $+\infty$. It provides the ambient–intrinsic identification needed to transfer statements between the two relaxed energy constructions, without imposing a density or second-moment assumption on $\mu$.
--
--   **Formalization Note** The energies take values in $[0,\infty]$ and are compared as extended-valued functionals. The statement is restricted to finite-dimensional real inner-product spaces and makes no assumption that the affine support has positive dimension.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.SmoothGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem relaxation_eq_intrinsic_energy :
--       relaxation μ = Intrinsic.energy μ
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/SmoothGradient/Intrinsic/Comparison`](https://prove2.me/theorems/c8ed0dde-2117-488a-be18-6aa1ac07ea16).
--
--   Definition modules: [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Energy/SmoothGradient/Intrinsic/Basic`](https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e), [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd).
--
--   Supporting theorems: [`toAmbientL2_toIntrinsicL2`](https://prove2.me/theorems/d9b94329-b8fa-4834-8b8e-906342810111), [`exists_ambient_extension`](https://prove2.me/theorems/eca5f601-3244-4c7a-abb0-b647df83122f).
--
--   Previous: [`exists_ambient_extension`](https://prove2.me/theorems/eca5f601-3244-4c7a-abb0-b647df83122f).
--
--   [Source excerpt, lines 183–184](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L183-L184) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L181-L204 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison`, declaration `FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison

universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)

theorem FunctionalInequalities.Energy.SmoothGradient.relaxation_eq_intrinsic_energy_readable :
    relaxation μ = Intrinsic.energy μ := by sorry
