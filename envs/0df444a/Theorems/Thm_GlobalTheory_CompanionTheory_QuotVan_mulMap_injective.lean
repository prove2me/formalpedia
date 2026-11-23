-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_mulMap_injective
-- name    : GlobalTheory.CompanionTheory.QuotVan.mulMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:21:21.879795+00:00
-- url     : https://prove2.me/theorems/8f9d10a2-7152-42ba-b9a7-dac5ddcb443b
-- title:
--   Quot Van: mul Map injective
-- statement:
--   The Quot Van construction uses the mul Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L141-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L141-L155

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

theorem GlobalTheory.CompanionTheory.QuotVan.mulMap_injective {Q : Type} [Group Q] (N M : Subgroup Q) (hinf : N ⊓ M = ⊥) :
    Function.Injective (fun p : N × M => (p.1 : Q) * (p.2 : Q)) := by sorry
