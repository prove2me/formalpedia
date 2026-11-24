-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_ip_ind
-- name    : GlobalTheory.CompanionTheory.MackeyFn.ip_ind
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:52:00.889847+00:00
-- url     : https://prove2.me/theorems/c5d53ff7-5eb7-457b-80d0-8f5c5d7c70c2
-- title:
--   Mackey Fn: ip ind
-- statement:
--   The Mackey Fn construction uses the ip ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L38-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L38-L61

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

theorem GlobalTheory.CompanionTheory.MackeyFn.ip_ind (A B : Subgroup Γ) (a b : Γ → ℂ) :
    ip (A : Set Γ) a (indF B b) =
      ((Nat.card A : ℂ)⁻¹ * (Nat.card B : ℂ)⁻¹) * ∑ x, mS A B a b x := by sorry
