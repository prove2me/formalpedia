-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeProduct_left_right_mul
-- name    : GlobalTheory.CompanionTheory.HeckeProduct.left_right_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:43.931155+00:00
-- url     : https://prove2.me/theorems/22b1ccd7-e400-4e5e-9b85-51ce204df6c7
-- title:
--   Hecke Product: left right mul
-- statement:
--   The Hecke Product construction uses the left right mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteSupportConvolutionTriple.lean#L117-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteSupportConvolutionTriple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeProduct
variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ (G₁ × G₂) V) (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)

theorem GlobalTheory.CompanionTheory.HeckeProduct.left_right_mul (g : G₁) (h : G₂) (u : V) :
    ρ (g, h) u = left ρ g (right ρ h u) := by sorry
