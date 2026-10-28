-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_smoothGradient_localDensity_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_smoothGradient_localDensity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:27.669276+00:00
-- url     : https://prove2.me/theorems/6f379ae6-5807-49ea-9f36-680203bb5799
-- title:
--   Existence of a Smooth-Gradient Local-Density Package
-- statement:
--   This auxiliary statement supplies a local-density package for a full-dimensional log-concave probability law.
--
--   Let $V$ be a finite-dimensional real inner product space with its Borel measurable structure and a second-countable topology. Let $m$ be an additive Haar measure on $V$, and $\nu$ a probability measure. Assume:
--
--   1. $\nu$ is log-concave (`KLS.LogConcave`).
--   2. The interior of its measure support is nonempty: $\operatorname{int}(\operatorname{supp}\nu)\ne\varnothing$.
--
--   Then the local-density structure is inhabited:
--   $$
--   \operatorname{Nonempty}\bigl(\operatorname{Energy.SmoothGradient.LocalDensity}(\nu,m)\bigr).
--   $$
--   The package provides an open full-measure region and density data, including positivity and local bounds for the reciprocal density, for use in smooth-core energy comparisons.
--
--   **Formalization Note** The conclusion is existence of the structure `Energy.SmoothGradient.LocalDensity`, not uniqueness or a canonical choice. Completeness is not an explicit hypothesis of this declaration.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_smoothGradient_localDensity (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) :
--       Nonempty (Energy.SmoothGradient.LocalDensity ν m)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Energy`](https://prove2.me/theorems/1c257615-0f8f-4176-ab61-d1bd2bbfd8f7).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/SmoothGradient/Core`](https://prove2.me/theorems/3df73178-e378-4d68-a6db-28967184707a).
--
--   [Source excerpt, lines 35–37](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Energy.lean#L35-L37) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Energy.lean#L32-L63 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Energy`, declaration `FunctionalInequalities.KLS.LogConcave.exists_smoothGradient_localDensity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Energy

open MeasureTheory Filter Topology
universe u
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
omit [CompleteSpace V]

theorem FunctionalInequalities.KLS.LogConcave.exists_smoothGradient_localDensity_readable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    Nonempty (Energy.SmoothGradient.LocalDensity ν m) := by sorry
