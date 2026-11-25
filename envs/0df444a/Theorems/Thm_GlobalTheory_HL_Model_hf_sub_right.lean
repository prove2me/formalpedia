-- Prove2me | Theorems.Thm_GlobalTheory_HL_Model_hf_sub_right
-- name    : GlobalTheory.HL.Model.hf_sub_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:39:12.520713+00:00
-- url     : https://prove2.me/theorems/d858a533-1011-476d-ae40-d29c3ae469ed
-- title:
--   Model: hf sub right
-- statement:
--   The Model construction uses the hf sub right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L29-L31

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

theorem GlobalTheory.HL.Model.hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H y (a - b) = hf L H y a - hf L H y b := by sorry
