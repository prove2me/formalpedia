-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pm_conj
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.pm_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:40.019744+00:00
-- url     : https://prove2.me/theorems/2cc798ba-60b2-4e9e-8553-bd9aa857504f
-- title:
--   Pm: pm conj
-- statement:
--   The Pm construction uses the pm conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L30-L44

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

theorem GlobalTheory.CompanionTheory.TyFin.Pm.pm_conj (σ : Equiv.Perm ι) (g : GL ι K) :
    pm K σ * g * (pm K σ)⁻¹ = glEquiv K σ g := by sorry
