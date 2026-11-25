-- Prove2me | Theorems.Thm_GlobalTheory_SA_PosOn_mono
-- name    : GlobalTheory.SA.PosOn.mono
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:22:58.5078+00:00
-- url     : https://prove2.me/theorems/a06c4067-243f-4d66-811d-9ed339e019a8
-- title:
--   Pos On: mono
-- statement:
--   The Pos On construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/CmStarOfIsCMUnram.lean#L35-L36

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
omit [NumberField E] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem GlobalTheory.SA.PosOn.mono {h : V →ₗ⋆[E] V →ₗ[E] E} {U U' : Submodule E V} (hU : PosOn h U) (hle : U' ≤ U) :
    PosOn h U' := by sorry
