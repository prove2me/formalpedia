-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_CuspIff_pm_conj
-- name    : GlobalTheory.CompanionTheory.TyFin.CuspIff.pm_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:55.887049+00:00
-- url     : https://prove2.me/theorems/c2c9e769-3289-42dd-b8e9-ee6157088e02
-- title:
--   Cusp Iff: pm conj
-- statement:
--   The Cusp Iff construction uses the pm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalOfUnipotentSumsVanish.lean#L57-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CuspidalOfUnipotentSumsVanish.lean#L57-L71

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CuspidalOfUnipotentSumsVanish
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
open Polynomial CategoryTheory
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.CuspIff

theorem GlobalTheory.CompanionTheory.TyFin.CuspIff.pm_conj {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (g : GL ι K) : pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by sorry
