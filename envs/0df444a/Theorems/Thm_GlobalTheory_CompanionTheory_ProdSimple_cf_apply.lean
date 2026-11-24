-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_ProdSimple_cf_apply
-- name    : GlobalTheory.CompanionTheory.ProdSimple.cf_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:56:23.506269+00:00
-- url     : https://prove2.me/theorems/e2b57452-fd71-44cb-bfa6-9f73fb87c614
-- title:
--   Prod Simple: cf apply
-- statement:
--   The Prod Simple construction uses the cf apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductSimpleAll.lean#L16-L16

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ProdSimple

theorem GlobalTheory.CompanionTheory.ProdSimple.cf_apply {Γ : Type} [Group Γ] (g : Γ) (a : MonoidAlgebra ℂ Γ) : cf g a = a.coeff g := by sorry
