-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_pm_eq_permGL
-- name    : GlobalTheory.CompanionTheory.TyFin.Bruhat.pm_eq_permGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:10.639304+00:00
-- url     : https://prove2.me/theorems/d0819862-100d-4c08-be1e-ec112d98c4e3
-- title:
--   Bruhat: pm eq perm GL
-- statement:
--   The Bruhat construction uses the pm eq perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L13-L13

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

theorem GlobalTheory.CompanionTheory.TyFin.Bruhat.pm_eq_permGL (σ : Equiv.Perm (Fin n)) : pm K σ = permGL K σ := by sorry
