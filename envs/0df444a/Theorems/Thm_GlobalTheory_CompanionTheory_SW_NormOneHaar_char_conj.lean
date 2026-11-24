-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_NormOneHaar_char_conj
-- name    : GlobalTheory.CompanionTheory.SW.NormOneHaar.char_conj
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:33.403067+00:00
-- url     : https://prove2.me/theorems/71fff4a5-02c9-4ade-b0bf-c442ef4e19b7
-- title:
--   Norm One Haar: char conj
-- statement:
--   The Norm One Haar construction uses the char conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean#L34-L44

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_MapMulEqOfNormOne
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.NormOneHaar
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem GlobalTheory.CompanionTheory.SW.NormOneHaar.char_conj (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) (u v : K)
    (h : u * v = 1) (h' : σ u * σ v = 1) :
    addEquivAddHaarChar (mulEquiv (σ u) (σ v) h') = addEquivAddHaarChar (mulEquiv u v h) := by sorry
