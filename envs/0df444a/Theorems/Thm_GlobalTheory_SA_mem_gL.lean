-- Prove2me | Theorems.Thm_GlobalTheory_SA_mem_gL
-- name    : GlobalTheory.SA.mem_gL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:52:23.800525+00:00
-- url     : https://prove2.me/theorems/42365c41-300e-431f-90af-2f9016382acc
-- title:
--   SA: mem g L
-- statement:
--   The SA construction uses the mem g L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean#L67-L72

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

theorem GlobalTheory.SA.mem_gL {S : HSpace E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (x : S.V) :
    x ∈ gL Λ g ↔ ∃ y ∈ Λ, (g : E) • y = x := by sorry
