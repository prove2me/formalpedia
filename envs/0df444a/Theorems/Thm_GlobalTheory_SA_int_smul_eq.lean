-- Prove2me | Theorems.Thm_GlobalTheory_SA_int_smul_eq
-- name    : GlobalTheory.SA.int_smul_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:57.111231+00:00
-- url     : https://prove2.me/theorems/113c00b5-11a9-4901-8526-9208cd9fd80a
-- title:
--   SA: int smul eq
-- statement:
--   The SA construction uses the int smul eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean#L30-L31

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_Spaces
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_CmStarOfIsCMUnram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SA
open NumberField Module Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
omit [NumberField E] [StarRing E]

theorem GlobalTheory.SA.int_smul_eq (c : 𝓞 E) (x : V) : c • x = (c : E) • x := by sorry
