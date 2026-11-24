-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_mS_inv
-- name    : GlobalTheory.CompanionTheory.MackeyFn.mS_inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:29.852326+00:00
-- url     : https://prove2.me/theorems/c367062e-4778-4cfa-acca-5c5f4609e041
-- title:
--   Mackey Fn: m S inv
-- statement:
--   The Mackey Fn construction uses the m S inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L63-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L63-L82

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

theorem GlobalTheory.CompanionTheory.MackeyFn.mS_inv {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    {β α : Γ} (x : Γ) (hβ : β ∈ B) (hα : α ∈ A) :
    mS A B a b (β * x * α) = mS A B a b x := by sorry
