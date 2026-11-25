-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NoethApprox_schemeModels
-- name    : GlobalTheory.CompanionTheory.NoethApprox.schemeModels
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:28:12.749106+00:00
-- url     : https://prove2.me/theorems/59763797-7270-4cfd-8988-3dab90e0d83b
-- title:
--   Noeth Approx: scheme Models
-- statement:
--   The Noeth Approx construction uses the scheme Models property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchemeModelsSpread.lean#L9-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchemeModelsSpread.lean#L9-L12

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SchemeDescendsToSubalgebra
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchemeModelsSpread
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GlobalTheory.SpreadingModels
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NoethApprox

theorem GlobalTheory.CompanionTheory.NoethApprox.schemeModels : GlobalTheory.SpreadingModels.SchemeModels := by sorry
