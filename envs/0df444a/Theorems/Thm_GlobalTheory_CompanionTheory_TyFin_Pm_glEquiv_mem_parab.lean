-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_mem_parab
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.glEquiv_mem_parab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:29.173694+00:00
-- url     : https://prove2.me/theorems/29fa43f5-1e02-4970-9ecc-5d36d3a5a2a3
-- title:
--   Pm: gl Equiv mem parab
-- statement:
--   The Pm construction uses the gl Equiv mem parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L57-L60

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

theorem GlobalTheory.CompanionTheory.TyFin.Pm.glEquiv_mem_parab {s : ℕ} (b : ι → Fin s) (σ : Equiv.Perm ι) (g : GL ι K) :
    glEquiv K σ g ∈ parab K b ↔ g ∈ parab K (b ∘ σ) := by sorry
