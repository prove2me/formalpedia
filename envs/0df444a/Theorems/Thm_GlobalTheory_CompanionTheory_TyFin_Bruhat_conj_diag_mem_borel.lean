-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_conj_diag_mem_borel
-- name    : GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_diag_mem_borel
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:17:53.180896+00:00
-- url     : https://prove2.me/theorems/c58d9e9c-9377-4e6e-b881-dabd0a1e7af2
-- title:
--   Bruhat: conj diag mem borel
-- statement:
--   The Bruhat construction uses the conj diag mem borel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L38-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L38-L43

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

theorem GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_diag_mem_borel (ρ : Equiv.Perm (Fin n)) {t : GL (Fin n) K}
    (ht : ∀ i j, i ≠ j → (t : Matrix (Fin n) (Fin n) K) i j = 0) :
    pm K ρ * t * (pm K ρ)⁻¹ ∈ borel n K := by sorry
