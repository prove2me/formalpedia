-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_UnitaryConv_conv_inf
-- name    : GlobalTheory.CompanionTheory.RgEis.UnitaryConv.conv_inf
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:26.79808+00:00
-- url     : https://prove2.me/theorems/c57d50a0-5068-495b-ac4d-c8849c0554a3
-- title:
--   Unitary Conv: conv inf
-- statement:
--   The Unitary Conv construction uses the conv inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L58-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/UnipotentConvergenceOfParabolic.lean#L58-L79

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UnipotentConvergenceOfParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis GlobalTheory.CompanionTheory.RgEis.UnitaryConv
open PositivityTheory.RgEis
variable {G : Type} [Group G]

theorem GlobalTheory.CompanionTheory.RgEis.UnitaryConv.conv_inf {Γ P₁ P₂ : Subgroup G} {l₁ l₂ : G → ℝ}
    (h₁ : ∀ γ ∈ Γ, γ ∈ P₁ → ∀ g, l₁ (γ * g) = l₁ g) (h₂ : ∀ γ ∈ Γ, γ ∈ P₂ → ∀ g, l₂ (γ * g) = l₂ g)
    (c₁ : Conv Γ P₁ l₁) (c₂ : Conv Γ P₂ l₂) : Conv Γ (P₁ ⊓ P₂) fun g => l₁ g + l₂ g := by sorry
