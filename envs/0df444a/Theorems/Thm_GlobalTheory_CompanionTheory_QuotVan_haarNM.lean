-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QuotVan_haarNM
-- name    : GlobalTheory.CompanionTheory.QuotVan.haarNM
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:04.434198+00:00
-- url     : https://prove2.me/theorems/4e7f8b1d-4ce2-4c9b-bb46-fbf0442d09f8
-- title:
--   Quot Van: haar NM
-- statement:
--   The Quot Van construction uses the haar NM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L157-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MapWithDensityEqOfScale.lean#L157-L210

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

theorem GlobalTheory.CompanionTheory.QuotVan.haarNM : HaarNM := by sorry
