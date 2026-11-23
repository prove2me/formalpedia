-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_map_conj
-- name    : GlobalTheory.CompanionTheory.QuotVan.map_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:03.124813+00:00
-- url     : https://prove2.me/theorems/d1b8ae79-8af2-49b6-a7fc-3f4e68c5abc5
-- title:
--   Quot Van: map conj
-- statement:
--   The Quot Van construction uses the map conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L80-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L80-L90

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

theorem GlobalTheory.CompanionTheory.QuotVan.map_conj (ν : Measure N) [ν.IsHaarMeasure] (m : M) :
    ν.map (conjCE N (m : Q)) = modInv N M m • ν := by sorry
