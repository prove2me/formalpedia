-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SmoothSpread_smooth_spreads
-- name    : GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:39.4798+00:00
-- url     : https://prove2.me/theorems/e7d922ec-8d39-4c7f-aedd-e8f37b33c258
-- title:
--   Smooth Spread: smooth spreads
-- statement:
--   The Smooth Spread construction uses the smooth spreads property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L216-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SmoothSpreadsOut.lean#L216-L234

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_CubeTheorem_SchemeModels
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SmoothSpreadsOut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct MvPolynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SmoothSpread

theorem GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads : GlobalTheory.SpreadingModels.Spreads (fun _ _ f ↦ Smooth f) := by sorry
