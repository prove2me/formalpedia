-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DwModel_isGaloisCover_complex
-- name    : GlobalTheory.ZM.DwModel.isGaloisCover_complex
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:09.003062+00:00
-- url     : https://prove2.me/theorems/46b7720a-3b1a-522d-93d1-a2b24c3918f1
-- title:
--   Dw Model: is Galois Cover complex
-- statement:
--   The Dw Model construction uses the is Galois Cover complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L82-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L82-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel

theorem GlobalTheory.ZM.DwModel.isGaloisCover_complex :
    IsGaloisCover (ℂ ≃ₐ[ℝ] ℂ) (fun σ => spMap (σ : ℂ →+* ℂ)) (spMap (algebraMap ℝ ℂ)) ∧ Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by sorry
