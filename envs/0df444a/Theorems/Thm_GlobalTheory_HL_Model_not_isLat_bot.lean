-- Prove2me | Theorems.Thm_GlobalTheory_HL_Model_not_isLat_bot
-- name    : GlobalTheory.HL.Model.not_isLat_bot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:21.334432+00:00
-- url     : https://prove2.me/theorems/1952d234-44b7-450f-939e-dbdc7f6834d0
-- title:
--   Model: not is Lat bot
-- statement:
--   The Model construction uses the not is Lat bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L156-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L156-L159

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

theorem GlobalTheory.HL.Model.not_isLat_bot (L : LocE F E) (n : ℕ) : ¬ IsLat L (⊥ : Submodule L.O (Fin (n + 1) → E)) := by sorry
