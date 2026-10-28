-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_Test_exists_ambient_extension_readable
-- name    : FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:46.391152+00:00
-- url     : https://prove2.me/theorems/eca5f601-3244-4c7a-abb0-b647df83122f
-- title:
--   Energy-Preserving Ambient Extension Of An Intrinsic Test
-- statement:
--   This theorem extends an intrinsic smooth-gradient test to the ambient space without changing its intrinsic restriction or raw energy.
--
--   Let $E$ be a finite-dimensional complete real inner-product normed space with its Borel measurable structure and second-countable topology, let $\mu$ be a probability measure on $E$, and let $g$ be a smooth-gradient test for the intrinsic measure associated with $\mu$. Then there exists an ambient smooth-gradient test $f$ such that, for every intrinsic coordinate $v$,
--
--   $$
--    f(\operatorname{reconstruct}_{\mu}(v))=g(v),
--   $$
--
--   and
--
--   $$
--   \operatorname{toIntrinsicL2}(\mu)(f.\operatorname{toL2})=g.\operatorname{toL2},
--   \qquad
--   f.\operatorname{energy}=g.\operatorname{energy}.
--   $$
--
--   The declaration is `exists_ambient_extension_readable`. The equality of energies is equality of the raw test-energy values, and the construction applies without a density or second-moment assumption on $\mu$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.SmoothGradient.Test`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_ambient_extension
--       (g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ)) :
--       ∃ f : Energy.SmoothGradient.Test μ,
--         (∀ v, f (Probability.reconstruct μ v) = g v) ∧
--         toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.energy = g.energy
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/SmoothGradient/Intrinsic/Comparison`](https://prove2.me/theorems/c8ed0dde-2117-488a-be18-6aa1ac07ea16).
--
--   Definition modules: [`Energy/SmoothGradient/Basic`](https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Energy/SmoothGradient/Intrinsic/Basic`](https://prove2.me/theorems/fd3da48f-6efa-4121-8307-74c1c05a7d2e).
--
--   Next: [`relaxation_eq_intrinsic_energy`](https://prove2.me/theorems/173a210b-c07a-4836-9df1-d0ac82ab944a).
--
--   [Source excerpt, lines 156–160](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L156-L160) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Intrinsic/Comparison.lean#L154-L177 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Intrinsic.Comparison`, declaration `FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Intrinsic_Comparison

open FunctionalInequalities.Energy.Euclidean
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
  (μ : MeasureTheory.ProbabilityMeasure E)

theorem FunctionalInequalities.Energy.SmoothGradient.Test.exists_ambient_extension_readable
    (g : Energy.SmoothGradient.Test (Probability.intrinsicMeasure μ)) :
    ∃ f : Energy.SmoothGradient.Test μ,
      (∀ v, f (Probability.reconstruct μ v) = g v) ∧
      toIntrinsicL2 μ f.toL2 = g.toL2 ∧ f.energy = g.energy := by sorry
