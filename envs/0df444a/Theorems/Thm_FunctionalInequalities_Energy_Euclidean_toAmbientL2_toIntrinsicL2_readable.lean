-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_Euclidean_toAmbientL2_toIntrinsicL2_readable
-- name    : FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:19.17609+00:00
-- url     : https://prove2.me/theorems/d9b94329-b8fa-4834-8b8e-906342810111
-- title:
--   Ambient Reconstruction After Intrinsic Coordinates
-- statement:
--   This is an identity for the ambient and intrinsic $L^2$ coordinate maps.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with its Borel measurable structure and second-countable topology, and let $\mu$ be a probability measure on $E$. For every element $f$ of $L^2(\mu)$, first map $f$ to intrinsic coordinates using `toIntrinsicL2`, and then map it back to ambient coordinates using `toAmbientL2`. The result is exactly $f$:
--
--   $$
--   \operatorname{toAmbientL2}(\mu)\bigl(\operatorname{toIntrinsicL2}(\mu)(f)\bigr)=f.
--   $$
--
--   The declaration is `toAmbientL2_toIntrinsicL2_readable`. No completeness assumption on $E$ is required by the declaration, and the equality is equality in the $L^2$ subtype rather than merely pointwise equality of representatives. This provides the retraction identity needed when comparing ambient and intrinsic energies.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.Euclidean`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   @[simp]
--   theorem toAmbientL2_toIntrinsicL2 (μ : ProbabilityMeasure E)
--       (f : Lp ℝ 2 (μ : Measure E)) :
--       toAmbientL2 μ (toIntrinsicL2 μ f) = f
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/SmoothGradient/Intrinsic/Basic`](https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e).
--
--   Definition modules: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   [Source excerpt, lines 48–51](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Basic.lean#L48-L51) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Basic.lean#L46-L74 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Basic`, declaration `FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Basic

open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]
omit [CompleteSpace E]

@[simp]
theorem FunctionalInequalities.Energy.Euclidean.toAmbientL2_toIntrinsicL2_readable (μ : ProbabilityMeasure E)
    (f : Lp ℝ 2 (μ : Measure E)) :
    toAmbientL2 μ (toIntrinsicL2 μ f) = f := by sorry
