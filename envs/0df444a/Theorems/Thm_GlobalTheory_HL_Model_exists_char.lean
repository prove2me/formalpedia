-- Prove2me | Theorems.Thm_GlobalTheory_HL_Model_exists_char
-- name    : GlobalTheory.HL.Model.exists_char
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:46:37.395848+00:00
-- url     : https://prove2.me/theorems/e7f23fe0-2f25-55cc-afae-292edd3e7992
-- title:
--   Model: exists char
-- statement:
--   The Model construction uses the exists char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L237-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L237-L270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_HermitianLattices
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.HL.Model.exists_char (a : F) (ha : a ∉ 𝒪[F]) :
    ∃ ψ : AddChar F ℂ, (∀ y ∈ 𝒪[F], ψ y = 1) ∧ ψ a ≠ 1 := by sorry
