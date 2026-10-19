-- Prove2me | Theorems.Thm_MazurTransfer_ContinuousFirstCohomologyTrivialTargetInjection_coefficientMap_injective
-- name    : MazurTransfer.ContinuousFirstCohomologyTrivialTargetInjection.coefficientMap_injective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-19T01:18:33.348892+00:00
-- url     : https://prove2.me/theorems/3d542955-30b2-4f17-adcb-e61c21e9fea8
-- statement:
--   An injective equivariant continuous coefficient map to a trivial group action induces an injective map on continuous first cohomology. The exact original complete hypotheses are retained. The downstream consumer is good-prime inertia vanishing for actual character-line Kummer lifts.

import Definitions.Def_MazurTransfer_ContinuousFirstCohomologyCoefficientMapData
noncomputable section

theorem MazurTransfer.ContinuousFirstCohomologyTrivialTargetInjection.coefficientMap_injective (G M N : Type) [Group G] [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    [TopologicalSpace G] [TopologicalSpace M] [TopologicalSpace N]
    [IsTopologicalGroup M] [IsTopologicalGroup N]
    (i : M →* N) (hi : Function.Injective i)
    (he : ∀ (g : G) (m : M), i (g • m) = g • i m) (hc : Continuous i)
    (hN : ∀ (g : G) (n : N), g • n = n) :
    Function.Injective (MazurTransfer.ContinuousFirstCohomologyCoefficientMap.coefficientMap G M N i he hc) := by sorry
