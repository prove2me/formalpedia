-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_map_translate
-- name    : GlobalTheory.CompanionTheory.QuotVan.map_translate
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:09.222567+00:00
-- url     : https://prove2.me/theorems/01cb8845-fb36-4681-a28e-3993099ed069
-- title:
--   Quot Van: map translate
-- statement:
--   The Quot Van construction uses the map translate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L116-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L116-L137

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

theorem GlobalTheory.CompanionTheory.QuotVan.map_translate (νN : Measure N) [νN.IsHaarMeasure] (νM : Measure M) [νM.IsHaarMeasure]
    [LocallyCompactSpace M] (u : N) (m : M) :
    ((νN.prod νM).withDensity fun p => modInv N M p.2).map
        (fun p : N × M => (u * conjCE N (m : Q) p.1, m * p.2)) =
      (νN.prod νM).withDensity fun p => modInv N M p.2 := by sorry
