-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_conj_pm_apply
-- name    : GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_pm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:44.93279+00:00
-- url     : https://prove2.me/theorems/850ffa95-0ecd-4719-bba7-ddda1828e4de
-- title:
--   Bruhat: conj pm apply
-- statement:
--   The Bruhat construction uses the conj pm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L15-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L15-L18

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_BruhatDecompositionTwoBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin Formalism.IrreducibleCountingLemmas.TYPES GroundTheory.Automorphic
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFin GlobalTheory.CompanionTheory.TyFin.Bruhat
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {n : ℕ}

theorem GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_pm_apply (τ : Equiv.Perm (Fin n)) (x : GL (Fin n) K) (i j : Fin n) :
    ((pm K τ * x * (pm K τ)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j =
      (x : Matrix (Fin n) (Fin n) K) (τ⁻¹ i) (τ⁻¹ j) := by sorry
