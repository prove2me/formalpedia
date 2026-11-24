-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_conj_mem_iff
-- name    : GlobalTheory.CompanionTheory.MackeyFn.conj_mem_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:55.242088+00:00
-- url     : https://prove2.me/theorems/91750a6f-39eb-4edb-834d-eaaafc7cfbe2
-- title:
--   Mackey Fn: conj mem iff
-- statement:
--   The Mackey Fn construction uses the conj mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L19-L26

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MackeyInnerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.MackeyFn
variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem GlobalTheory.CompanionTheory.MackeyFn.conj_mem_iff (H : Subgroup Γ) {u h : Γ} (hu : u ∈ H) : u * h * u⁻¹ ∈ H ↔ h ∈ H := by sorry
