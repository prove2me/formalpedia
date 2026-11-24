-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_pm_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.pm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:44.20131+00:00
-- url     : https://prove2.me/theorems/b9ec4f27-67bf-49a3-ae34-36e47c141210
-- title:
--   Pm: pm apply
-- statement:
--   The Pm construction uses the pm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L13-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L13-L23

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

theorem GlobalTheory.CompanionTheory.TyFin.Pm.pm_apply (σ : Equiv.Perm ι) (i j : ι) :
    (pm K σ : Matrix ι ι K) i j = if i = σ j then 1 else 0 := by sorry
