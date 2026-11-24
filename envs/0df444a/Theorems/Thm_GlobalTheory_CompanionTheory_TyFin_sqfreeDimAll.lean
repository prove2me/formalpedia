-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_sqfreeDimAll
-- name    : GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:09:26.818332+00:00
-- url     : https://prove2.me/theorems/9967efc9-3b4c-4480-9cb5-802c212883af
-- title:
--   Ty Fin: sqfree Dim All
-- statement:
--   The Ty Fin construction uses the sqfree Dim All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquarefreeDimensionFormula.lean#L18-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SquarefreeDimensionFormula.lean#L18-L65

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardParabolicSubgroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimensionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SquarefreeDimensionFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.sqfreeDimAll : ReciprocityTheory.Ty.Fin.St.SqfreeDimAll := by sorry
