-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_of_continuousLinearEquiv_map_readable
-- name    : FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:15.55451+00:00
-- url     : https://prove2.me/theorems/c637e7db-3431-42d0-bb61-ac5baf6882b0
-- title:
--   Log-Concavity Under Inverse Continuous Linear Equivalence
-- statement:
--   This statement shows that log-concavity pulls back through a continuous linear equivalence when its pushforward law is log-concave.
--
--   Let $E$ and $F$ be real normed vector spaces, each equipped with a Borel measurable structure. Let $μ$ be a probability measure on $E$ and let $ν$ be a probability measure on $F$. Assume:
--
--   1. $μ$ is log-concave.
--   2. $T : F → E$ is a continuous linear equivalence over $ℝ$.
--   3. The pushforward of $ν$ by $T$ is $μ$:
--
--   $$T_*ν = μ.$$
--
--   Then $ν$ is log-concave:
--
--   $$ν\text{ is log-concave}.$$
--
--   This provides a reusable change-of-space principle for log-concave probability laws, without requiring inner-product or finite-dimensional structure in either space.
--
--   **Formalization Note** The conclusion is the predicate `KLS.LogConcave`; the pushforward equation is Lean's `Measure.map` equality after coercing the probability measures to measures. The map $T$ is a continuous linear equivalence, so both $T$ and its inverse are continuous and injective.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem of_continuousLinearEquiv_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
--       (ν : ProbabilityMeasure F) (T : F ≃L[ℝ] E)
--       (hmap : Measure.map T (ν : Measure F) = (μ : Measure E)) : LogConcave ν
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Isotropic`](https://prove2.me/theorems/35471368-b77f-4600-8554-699e6845e252).
--
--   Definition modules: [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Next: [`exists_isotropic_localSlope_constant_eq`](https://prove2.me/theorems/5dfc02d9-caf9-4e32-9ec6-e921e0672aed).
--
--   [Source excerpt, lines 61–63](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean#L61-L63) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean#L59-L89 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Isotropic`, declaration `FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic

open MeasureTheory Filter Topology InnerProductSpace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

theorem FunctionalInequalities.KLS.LogConcave.of_continuousLinearEquiv_map_readable {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (ν : ProbabilityMeasure F) (T : F ≃L[ℝ] E)
    (hmap : Measure.map T (ν : Measure F) = (μ : Measure E)) : LogConcave ν := by sorry
