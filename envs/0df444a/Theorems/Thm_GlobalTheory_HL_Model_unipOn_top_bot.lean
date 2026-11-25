-- Prove2me | Theorems.Thm_GlobalTheory_HL_Model_unipOn_top_bot
-- name    : GlobalTheory.HL.Model.unipOn_top_bot
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:06:21.571663+00:00
-- url     : https://prove2.me/theorems/9a1359f8-eecc-414f-ab1a-dfc64c6277a4
-- title:
--   Model: unip On top bot
-- statement:
--   The Model construction uses the unip On top bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L164-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsIntegralIff.lean#L164-L169

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

theorem GlobalTheory.HL.Model.unipOn_top_bot {n : ℕ} : unipOn (E := E) (n := n) ⊤ ⊥ = ⊥ := by sorry
