-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_NormOneHaar_map_mul_eq_of_norm_one
-- name    : GlobalTheory.CompanionTheory.SW.NormOneHaar.map_mul_eq_of_norm_one
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:18.642046+00:00
-- url     : https://prove2.me/theorems/07ecb194-abe3-4210-a287-7121d757b62c
-- title:
--   Norm One Haar: map mul eq of norm one
-- statement:
--   The Norm One Haar construction uses the map mul eq of norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean#L54-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/MapMulEqOfNormOne.lean#L54-L73

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

theorem GlobalTheory.CompanionTheory.SW.NormOneHaar.map_mul_eq_of_norm_one :
    ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
      [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (σ : K →+* K),
      Continuous σ → (∀ y, σ (σ y) = y) → ∀ (lam : Measure K) [lam.IsAddHaarMeasure] (u : K),
      u * σ u = 1 → lam.map (fun y => u * y) = lam := by sorry
