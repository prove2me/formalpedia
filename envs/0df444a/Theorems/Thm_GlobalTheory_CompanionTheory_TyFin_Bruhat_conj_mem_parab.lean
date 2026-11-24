-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_TyFin_Bruhat_conj_mem_parab
-- name    : GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_mem_parab
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:58.556665+00:00
-- url     : https://prove2.me/theorems/2bf2301a-0802-46a7-bd3f-f9c7bb813c01
-- title:
--   Bruhat: conj mem parab
-- statement:
--   The Bruhat construction uses the conj mem parab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/BruhatDecompositionTwoBlocks.lean#L30-L36

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

theorem GlobalTheory.CompanionTheory.TyFin.Bruhat.conj_mem_parab {s : ℕ} (b : Fin n → Fin s) (τ : Equiv.Perm (Fin n))
    (hτ : Monotone (b ∘ τ)) {x : GL (Fin n) K} (hx : x ∈ borel n K) :
    pm K τ * x * (pm K τ)⁻¹ ∈ parab K b := by sorry
