-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_Avg_isPat_colGe
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.isPat_colGe
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:48.307901+00:00
-- url     : https://prove2.me/theorems/ca701cef-2445-43c9-a38f-6ade35f68497
-- title:
--   Avg: is Pat col Ge
-- statement:
--   The Avg construction uses the is Pat col Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WhittakerVanishesOfRadicalSums.lean#L58-L59

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WhittakerVanishesOfRadicalSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep GlobalTheory.CompanionTheory.TyFin.ColStep.Avg

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.isPat_colGe (d j : ℕ) : IsPat (colGe d j) := by sorry
