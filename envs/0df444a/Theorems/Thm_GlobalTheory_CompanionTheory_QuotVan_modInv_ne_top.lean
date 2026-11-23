-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_modInv_ne_top
-- name    : GlobalTheory.CompanionTheory.QuotVan.modInv_ne_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:12:50.326744+00:00
-- url     : https://prove2.me/theorems/5ba3511c-5b8f-4e25-969e-b9e28a51ba6b
-- title:
--   Quot Van: mod Inv ne top
-- statement:
--   The Quot Van construction uses the mod Inv ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L67-L69

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

theorem GlobalTheory.CompanionTheory.QuotVan.modInv_ne_top (m : M) : modInv N M m ≠ ∞ := by sorry
