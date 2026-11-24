-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_MackeyFn_sum_dc
-- name    : GlobalTheory.CompanionTheory.MackeyFn.sum_dc
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:52:08.618189+00:00
-- url     : https://prove2.me/theorems/43e88e9a-5c38-4d7c-9349-e691466e6191
-- title:
--   Mackey Fn: sum dc
-- statement:
--   The Mackey Fn construction uses the sum dc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L134-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MackeyInnerProduct.lean#L134-L147

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

theorem GlobalTheory.CompanionTheory.MackeyFn.sum_dc {A B : Subgroup Γ} {a b : Γ → ℂ} (hA : IsClassOn A a) (hB : IsClassOn B b)
    (g : Γ) [DecidablePred (· ∈ dc A B g)] :
    (∑ x, if x ∈ dc A B g then mS A B a b x else 0) = (Nat.card (dc A B g) : ℂ) * mS A B a b g := by sorry
