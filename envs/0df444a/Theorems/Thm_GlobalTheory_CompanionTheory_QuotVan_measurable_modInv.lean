-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_measurable_modInv
-- name    : GlobalTheory.CompanionTheory.QuotVan.measurable_modInv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:59.463804+00:00
-- url     : https://prove2.me/theorems/d2a80d27-30e4-4c6c-91e2-f381c1ff1742
-- title:
--   Quot Van: measurable mod Inv
-- statement:
--   The Quot Van construction uses the measurable mod Inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L92-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L92-L114

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TopoPolish
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MapWithDensityEqOfScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QuotVan
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [MeasurableSpace Q] [BorelSpace Q] [SecondCountableTopology Q] [T2Space Q]
variable (N M : Subgroup Q) [N.Normal] [LocallyCompactSpace N] [SecondCountableTopology N]
  [SecondCountableTopology M]

theorem GlobalTheory.CompanionTheory.QuotVan.measurable_modInv : Measurable (modInv N M) := by sorry
