-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_NormOneHaar_char_mul_eq_one
-- name    : GlobalTheory.CompanionTheory.SW.NormOneHaar.char_mul_eq_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:08:20.637583+00:00
-- url     : https://prove2.me/theorems/93087db9-3d21-4d9c-a23f-33b530ece468
-- title:
--   Norm One Haar: char mul eq one
-- statement:
--   The Norm One Haar construction uses the char mul eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean#L46-L52

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

theorem GlobalTheory.CompanionTheory.SW.NormOneHaar.char_mul_eq_one (u v : K) (h : u * v = 1) (h' : v * u = 1) :
    addEquivAddHaarChar (mulEquiv u v h) * addEquivAddHaarChar (mulEquiv v u h') = 1 := by sorry
