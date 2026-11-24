-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RootExch_one_side
-- name    : GlobalTheory.CompanionTheory.RootExch.one_side
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:08.501214+00:00
-- url     : https://prove2.me/theorems/e1169f55-671c-4e1a-892e-f853376c9415
-- title:
--   Root Exch: one side
-- statement:
--   The Root Exch construction uses the one side property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L72-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/RootExchange.lean#L72-L98

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {G : Type*} [Group G] [Fintype G]
open Classical

theorem GlobalTheory.CompanionTheory.RootExch.one_side (P Q : Subgroup G) (lam χ : G → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g)
    (hm : ∀ a ∈ P, ∀ b ∈ P, lam (a * b) = lam a * lam b) (hne : ∀ a ∈ P, lam a ≠ 0)
    (hPQ : ∀ v ∈ Q, v ∉ P → ∃ h ∈ P, h * v * h⁻¹ * v⁻¹ ∈ P ∧ lam (h * v * h⁻¹ * v⁻¹) ≠ 1) :
    (∑ v, if v ∈ Q then (lam v)⁻¹ * (∑ u, if u ∈ P then (lam u)⁻¹ * χ (u * v) else 0) else 0) =
      ((Finset.univ.filter fun v => v ∈ P ∧ v ∈ Q).card : ℂ) *
        ∑ u, if u ∈ P then (lam u)⁻¹ * χ u else 0 := by sorry
