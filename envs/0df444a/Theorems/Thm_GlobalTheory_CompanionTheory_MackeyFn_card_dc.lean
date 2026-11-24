-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_card_dc
-- name    : GlobalTheory.CompanionTheory.MackeyFn.card_dc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:51:59.082776+00:00
-- url     : https://prove2.me/theorems/1ef653db-bbba-4589-a3cd-0b99103590d7
-- title:
--   Mackey Fn: card dc
-- statement:
--   The Mackey Fn construction uses the card dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L84-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L84-L132

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

theorem GlobalTheory.CompanionTheory.MackeyFn.card_dc (A B : Subgroup Γ) (g : Γ) :
    Nat.card (dc A B g) * Nat.card (A ⊓ cj g B : Subgroup Γ) = Nat.card A * Nat.card B := by sorry
