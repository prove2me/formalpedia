-- Prove2me | Theorems.Thm_GlobalTheory_HL_Model_hf_single
-- name    : GlobalTheory.HL.Model.hf_single
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:51.051186+00:00
-- url     : https://prove2.me/theorems/3ddd9ddd-0570-451c-aa7e-67832c7337aa
-- title:
--   Model: hf single
-- statement:
--   The Model construction uses the hf single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L52-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L52-L54

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

theorem GlobalTheory.HL.Model.hf_single (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    hf L H (Pi.single i 1) (Pi.single j 1) = H i j := by sorry
