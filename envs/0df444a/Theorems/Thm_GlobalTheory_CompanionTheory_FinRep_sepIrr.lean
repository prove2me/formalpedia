-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FinRep_sepIrr
-- name    : GlobalTheory.CompanionTheory.FinRep.sepIrr
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:41:24.283134+00:00
-- url     : https://prove2.me/theorems/2d5dbcba-8501-4ee8-970e-e530090a39ee
-- title:
--   Fin Rep: sep Irr
-- statement:
--   The Fin Rep construction uses the sep Irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducible.lean#L66-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SeparableIrreducible.lean#L66-L93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SeparableIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FinRep
variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem GlobalTheory.CompanionTheory.FinRep.sepIrr : ReciprocityTheory.Ty.Fin.St.SepIrr := by sorry
