-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Pm_glEquiv_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.Pm.glEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:19.277698+00:00
-- url     : https://prove2.me/theorems/79974706-e61f-4c61-875c-6d19b96ea0ad
-- title:
--   Pm: gl Equiv apply
-- statement:
--   The Pm construction uses the gl Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PermutationMatrixProperties.lean#L27-L28

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

theorem GlobalTheory.CompanionTheory.TyFin.Pm.glEquiv_apply {κ : Type} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (g : GL ι K) (i j : κ) :
    (glEquiv K e g : Matrix κ κ K) i j = (g : Matrix ι ι K) (e.symm i) (e.symm j) := by sorry
