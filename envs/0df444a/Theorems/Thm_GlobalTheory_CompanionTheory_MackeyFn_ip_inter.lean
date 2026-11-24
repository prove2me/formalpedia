-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_ip_inter
-- name    : GlobalTheory.CompanionTheory.MackeyFn.ip_inter
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:02.322066+00:00
-- url     : https://prove2.me/theorems/588e4c6f-2764-4ed0-81b4-67501572867c
-- title:
--   Mackey Fn: ip inter
-- statement:
--   The Mackey Fn construction uses the ip inter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L28-L36

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

theorem GlobalTheory.CompanionTheory.MackeyFn.ip_inter (A B : Subgroup Γ) (a b : Γ → ℂ) (y : Γ) :
    ip ((A ⊓ cj y B : Subgroup Γ) : Set Γ) a (fun h => b (y * h * y⁻¹)) =
      (Nat.card (A ⊓ cj y B : Subgroup Γ) : ℂ)⁻¹ * mS A B a b y := by sorry
