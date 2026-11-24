-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_FouSB_fou_sb
-- name    : GlobalTheory.CompanionTheory.SW.FouSB.fou_sb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:10.220715+00:00
-- url     : https://prove2.me/theorems/ec566218-dfb5-4b21-82bd-3d1680f4ae0b
-- title:
--   Fou SB: fou sb
-- statement:
--   The Fou SB construction uses the fou sb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FourierInversionSchwartzBruhat.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/FourierInversionSchwartzBruhat.lean#L9-L10

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_WeilImplicationNonarchQuadratic
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_FourierInversionSchwartzBruhat
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_fou_sb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FouSB

theorem GlobalTheory.CompanionTheory.SW.FouSB.fou_sb : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (χ : V → V → ℂ) (μ : Measure V), NADual V χ μ → ∀ φ : V → ℂ, SB φ → SB (fou χ μ φ) ∧ ∀ x, fou χ μ (fou χ μ φ) x = φ (-x) := by sorry
