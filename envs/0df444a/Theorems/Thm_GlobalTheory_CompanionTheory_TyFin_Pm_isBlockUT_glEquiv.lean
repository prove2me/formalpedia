-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_isBlockUT_glEquiv
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.isBlockUT_glEquiv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:19:02.451729+00:00
-- url     : https://prove2.me/theorems/37397329-6022-47be-b9a6-5354bfe73a46
-- title:
--   Pm: is Block UT gl Equiv
-- statement:
--   The Pm construction uses the is Block UT gl Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L47-L55

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PermutationMatrixProperties
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Pm
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
omit [Fintype K] [DecidableEq K]

theorem GlobalTheory.CompanionTheory.TyFin.Pm.isBlockUT_glEquiv {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    IsBlockUT K b (glEquiv K σ g : Matrix ι ι K) ↔ IsBlockUT K (b ∘ σ) (g : Matrix ι ι K) := by sorry
