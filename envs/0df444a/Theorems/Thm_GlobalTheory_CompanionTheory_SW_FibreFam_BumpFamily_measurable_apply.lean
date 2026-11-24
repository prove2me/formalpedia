-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_measurable_apply
-- name    : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:04:11.752382+00:00
-- url     : https://prove2.me/theorems/5be346a5-5625-4048-9bb5-632e175894b3
-- title:
--   Bump Family: measurable apply
-- statement:
--   The Bump Family construction uses the measurable apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L127-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L127-L155

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

theorem GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.measurable_apply [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hB : IsOpen B) (hU : IsOpen U) (hc : ∀ b, fib b Uᶜ = 0)
    {A : Set V} (hA : MeasurableSet A) : Measurable fun b => fib b A := by sorry
