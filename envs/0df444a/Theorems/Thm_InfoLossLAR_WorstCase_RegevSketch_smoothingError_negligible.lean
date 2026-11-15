-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_smoothingError_negligible
-- name    : InfoLossLAR.WorstCase.RegevSketch.smoothingError_negligible
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:24:45.894094+00:00
-- url     : https://prove2.me/theorems/6bd579e2-5428-4cb8-af37-e05b5af20fe4
-- title:
--   The fixed logarithmic smoothing schedule is negligible
-- statement:
--   The one fixed function $\epsilon(n)=2^{-\operatorname{size}(n+2)^2}$ is nonnegative at every natural number and negligible in the published security sense: for every positive real constant $c$, there is a threshold $n_0$ such that $\epsilon(n)\le n^{-c}$ for every $n\ge n_0$. Here size is the natural-number binary length. The schedule is fixed independently of any distinguisher, source-basis encoding length, sample polynomial or accuracy exponent. This statement concerns the explicitly defined numerical function only; it does not claim existence of a DGS sampler or a lattice-solving algorithm.
-- source:
--   Existing locally checked proof: Solutions/RegevBridgeNegligibleSmoothingError.lean (fixedSmoothingError_negligible) and Solutions/RegevBridgeGaussianVerification.lean (platform_negligible_of_native), combined in Solutions/RegevBridgeFixedLogSmoothing.lean (fixedSmoothingError_platform_negligible). Reused under the definitionally identical schedule in the published InfoLossLAR_RegevSketch_DGS definition; no new mathematical assumption.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open QAlgorithms.Complexity

namespace InfoLossLAR.WorstCase.RegevSketch

theorem smoothingError_negligible : InfoLossLAR.WorstCase.Negligible smoothingError := by sorry

end InfoLossLAR.WorstCase.RegevSketch
