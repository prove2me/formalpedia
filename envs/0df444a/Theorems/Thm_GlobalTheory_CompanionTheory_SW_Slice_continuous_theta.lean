-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_continuous_theta
-- name    : GlobalTheory.CompanionTheory.SW.Slice.continuous_theta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:11:00.545467+00:00
-- url     : https://prove2.me/theorems/b615f5e9-067e-4d7c-8365-de3e59ed80f0
-- title:
--   Slice: continuous theta
-- statement:
--   The Slice construction uses the continuous theta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L71-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L71-L72

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MeasureEqHaarProdOfLeftInvariant
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Slice
variable {V X Q : Type} [TopologicalSpace V] [TopologicalSpace X] [Group Q] [TopologicalSpace Q]
  [IsTopologicalGroup Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X]

theorem GlobalTheory.CompanionTheory.SW.Slice.continuous_theta (g : V → X) (b₀ : X) : Continuous (theta (Q := Q) g b₀) := by sorry
