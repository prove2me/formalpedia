-- Prove2me | Theorems.Thm_GlobalTheory_HL_Model_invVol_of_le
-- name    : GlobalTheory.HL.Model.invVol_of_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:08.528556+00:00
-- url     : https://prove2.me/theorems/0c9c63cd-2c7f-58ca-8f7d-69076984809b
-- title:
--   Model: inv Vol of le
-- statement:
--   The Model construction uses the inv Vol of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L174-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L174-L176

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

theorem GlobalTheory.HL.Model.invVol_of_le {G : Type*} [Group G] {K0 K : Subgroup G} (h : K ≤ K0) :
    invVol K0 K = K.relIndex K0 := by sorry
