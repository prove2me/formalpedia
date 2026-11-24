-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_conjCE_coe
-- name    : GlobalTheory.CompanionTheory.QuotVan.conjCE_coe
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:57:51.300494+00:00
-- url     : https://prove2.me/theorems/66f00a23-ba15-478e-b44a-e7357ad29bed
-- title:
--   Quot Van: conj CE coe
-- statement:
--   The Quot Van construction uses the conj CE coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L52-L53

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

theorem GlobalTheory.CompanionTheory.QuotVan.conjCE_coe (N : Subgroup Q) [N.Normal] (g : Q) (u : N) :
    ((conjCE N g u : N) : Q) = g * u * g⁻¹ := by sorry
