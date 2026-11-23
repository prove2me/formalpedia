-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Slice_theta_isOpenEmbedding
-- name    : GlobalTheory.CompanionTheory.SW.Slice.theta_isOpenEmbedding
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:55.231466+00:00
-- url     : https://prove2.me/theorems/09c3834b-d7ac-49e9-8968-986b4ce74328
-- title:
--   Slice: theta is Open Embedding
-- statement:
--   The Slice construction uses the theta is Open Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L74-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityFormula.lean#L74-L131

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

theorem GlobalTheory.CompanionTheory.SW.Slice.theta_isOpenEmbedding [T2Space X] {g : V → X} (hg : Continuous g)
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) {b₀ : X}
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    IsOpenEmbedding (theta (Q := Q) g b₀) ∧
      Set.range (theta (Q := Q) g b₀) = g ⁻¹' Set.range (fun q : Q => q • b₀) := by sorry
