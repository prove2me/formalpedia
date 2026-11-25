-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_simpleIffIrr
-- name    : GlobalTheory.CompanionTheory.TyFin.simpleIffIrr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:33.365564+00:00
-- url     : https://prove2.me/theorems/c6b318c1-eddb-4760-8fa6-8a7261d51f82
-- title:
--   Ty Fin: simple Iff Irr
-- statement:
--   The Ty Fin construction uses the simple Iff Irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SimpleIffIrreducible.lean#L118-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SimpleIffIrreducible.lean#L118-L120

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HarishChandraLabels_Basics
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin PI.GreenHCLabel
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin

theorem GlobalTheory.CompanionTheory.TyFin.simpleIffIrr : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by sorry
