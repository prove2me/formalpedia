-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_blkGL_glEquiv
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.blkGL_glEquiv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:34.973642+00:00
-- url     : https://prove2.me/theorems/48e9bcdb-8d8b-45fb-bbe4-16a3a13a4af1
-- title:
--   Pm: blk GL gl Equiv
-- statement:
--   The Pm construction uses the blk GL gl Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L67-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L67-L83

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

theorem GlobalTheory.CompanionTheory.TyFin.Pm.blkGL_glEquiv {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (c : Fin s) (g : GL ι K)
    (e : {i // (b ∘ σ) i = c} ≃ {j // b j = c})
    (he : ∀ x, (e x : ι) = σ x) :
    blkGL b c (glEquiv K σ g) = glEquiv K e (blkGL (b ∘ σ) c g) := by sorry
