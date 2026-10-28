-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_SmoothGradient_LocalDensity_subset_support_readable
-- name    : FunctionalInequalities.Energy.SmoothGradient.LocalDensity.subset_support_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:07:01.466447+00:00
-- url     : https://prove2.me/theorems/4329dc1d-2277-4ded-bce3-2accbe5d4636
-- title:
--   Local-Density Region Lies In The Measure Support
-- statement:
--   This lemma places the open local-density region inside the support of the probability measure.
--
--   Let $V$ be a normed additive group with a measurable Borel structure. Let $\nu$ be a probability measure on $V$, let $m$ be an additive Haar measure, and let $D$ be a `SmoothGradient.LocalDensity` for $(\nu,m)$. If $\Omega=D.\Omega$ denotes its designated open density region, then
--
--   $$
--   \Omega\subseteq\operatorname{supp}(\nu).
--   $$
--
--   The declaration is `subset_support_readable`. No inner-product, completeness, finite-dimensionality, or second-countability assumptions are included in the theorem type. The result is a support-membership fact used by the smooth-gradient density framework.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.SmoothGradient.LocalDensity`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subset_support : D.Ω ⊆ (ν : Measure V).support
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/SmoothGradient/Core`](https://prove2.me/theorems/3df73178-e378-4d68-a6db-28967184707a).
--
--   Next: [`Test.exists_domain_sequence_tendsto`](https://prove2.me/theorems/751a102a-9a04-4eaa-a613-041165658667).
--
--   [Source excerpt, lines 93–93](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L93-L93) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Core.lean#L91-L110 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Core`, declaration `FunctionalInequalities.Energy.SmoothGradient.LocalDensity.subset_support`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Core

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} {m : MeasureTheory.Measure V} (D : FunctionalInequalities.Energy.SmoothGradient.LocalDensity ν m)
variable [m.IsAddHaarMeasure]
omit [InnerProductSpace ℝ V] [CompleteSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]

theorem FunctionalInequalities.Energy.SmoothGradient.LocalDensity.subset_support_readable : D.Ω ⊆ (ν : Measure V).support := by sorry
