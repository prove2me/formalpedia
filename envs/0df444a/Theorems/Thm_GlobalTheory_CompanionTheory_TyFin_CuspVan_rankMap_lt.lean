-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspVan_rankMap_lt
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspVan.rankMap_lt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:57.277167+00:00
-- url     : https://prove2.me/theorems/e9c571ab-d0be-44cc-b994-8241ea141d2c
-- title:
--   Cusp Van: rank Map lt
-- statement:
--   The Cusp Van construction uses the rank Map lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalVanishing.lean#L77-L81

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalVanishing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspVan
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.CompanionTheory.TyFin.CuspVan.rankMap_lt {κ : Type} [Fintype κ] {s : ℕ} (β : κ → Fin s) (i j : κ) :
    rankMap β i < rankMap β j ↔ β i < β j := by sorry
