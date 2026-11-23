-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_eq_of_setLIntegral_compact_eq
-- name    : GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:44:27.788276+00:00
-- url     : https://prove2.me/theorems/593257bc-4f08-4ab8-a48d-27c0a8c86df0
-- title:
--   SW: eq of set LIntegral compact eq
-- statement:
--   The SW construction uses the eq of set LIntegral compact eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousDensitiesEqOfIntegralsOnCompacts.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ContinuousDensitiesEqOfIntegralsOnCompacts.lean#L38-L48

import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW

theorem GlobalTheory.CompanionTheory.SW.eq_of_setLIntegral_compact_eq :
    ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
      [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
      [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B →
      ContinuousOn D' B →
      (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) →
      ∀ b ∈ B, D b = D' b := by sorry
