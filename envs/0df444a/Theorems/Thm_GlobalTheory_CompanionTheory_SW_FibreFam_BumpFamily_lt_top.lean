-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FibreFam_BumpFamily_lt_top
-- name    : GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.lt_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:32.258793+00:00
-- url     : https://prove2.me/theorems/1b4d9325-0f75-48bc-959b-23b0594c3c9f
-- title:
--   Bump Family: lt top
-- statement:
--   The Bump Family construction uses the lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L116-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/DisintegrationDensityContinuous.lean#L116-L125

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

theorem GlobalTheory.CompanionTheory.SW.FibreFam.BumpFamily.lt_top [LocallyCompactSpace V] [T2Space V]
    {U : Set V} {B : Set X} {fib : X → Measure V}
    (h : BumpFamily U B fib) (hU : IsOpen U) {K : Set V} (hK : IsCompact K) (hKU : K ⊆ U) (b : X) :
    fib b K < ∞ := by sorry
