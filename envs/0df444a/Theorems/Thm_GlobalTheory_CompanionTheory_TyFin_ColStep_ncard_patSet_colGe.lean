-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_ColStep_ncard_patSet_colGe
-- name    : GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:14.621014+00:00
-- url     : https://prove2.me/theorems/85cecc79-dda3-4a29-aa5d-833968f0df90
-- title:
--   Col Step: ncard pat Set col Ge
-- statement:
--   The Col Step construction uses the ncard pat Set col Ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternSetCardColumnStep.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PatternSetCardColumnStep.lean#L62-L65

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ColGeR
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternSetCardColumnStep
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.ColStep

theorem GlobalTheory.CompanionTheory.TyFin.ColStep.ncard_patSet_colGe (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by sorry
