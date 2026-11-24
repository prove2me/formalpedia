-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_measurable_lintegral
-- name    : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_lintegral
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:04:46.135454+00:00
-- url     : https://prove2.me/theorems/ef46ae1b-7056-434c-bc25-0f6b15238dfe
-- title:
--   Bump Family: measurable lintegral
-- statement:
--   The Bump Family construction uses the measurable lintegral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L79-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L79-L95

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityContinuous
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FibreFam
variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_lintegral {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) {φ : V → ℝ} (hc : Continuous φ)
    (hcs : HasCompactSupport φ) (hs : tsupport φ ⊆ U) (h0 : ∀ v, 0 ≤ φ v) :
    Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b) := by sorry
