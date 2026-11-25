-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_prodSimpleAll
-- name    : GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:20.195742+00:00
-- url     : https://prove2.me/theorems/2c7c9d4a-9a1b-468c-b6d5-42d879c8e4f2
-- title:
--   Prod Simple: prod Simple All
-- statement:
--   The Prod Simple construction uses the prod Simple All property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L170-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L170-L190

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin CategoryTheory
noncomputable section
open GlobalTheory.CompanionTheory.ProdSimple

theorem GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll : ReciprocityTheory.Ty.Fin.St.ProdSimpleAll := by sorry
