-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_exists_diag_mul_uni
-- name    : GlobalTheory.CompanionTheory.TyFin.Bruhat.exists_diag_mul_uni
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:18:05.754101+00:00
-- url     : https://prove2.me/theorems/93cdf1f0-a02c-460e-8279-29581b5d7b30
-- title:
--   Bruhat: exists diag mul uni
-- statement:
--   The Bruhat construction uses the exists diag mul uni property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L45-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L45-L61

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

theorem GlobalTheory.CompanionTheory.TyFin.Bruhat.exists_diag_mul_uni {y : GL (Fin n) K} (hy : y ∈ borel n K) :
    ∃ t : GL (Fin n) K, (∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) ∧
      ∃ u ∈ patSet K (fun i j : Fin n => i < j), y = t⁻¹ * u := by sorry
