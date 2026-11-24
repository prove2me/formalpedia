-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_hcDim
-- name    : GlobalTheory.CompanionTheory.TyFin.hcDim
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:35:10.771957+00:00
-- url     : https://prove2.me/theorems/2261c623-60f3-4310-9e7c-071717cebd96
-- title:
--   Ty Fin: hc Dim
-- statement:
--   The Ty Fin construction uses the hc Dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraDimension.lean#L28-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HarishChandraDimension.lean#L28-L46

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraCharacterStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HarishChandraDimension
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

theorem GlobalTheory.CompanionTheory.TyFin.hcDim : ReciprocityTheory.Ty.Fin.St.HCDim := by sorry
