-- Prove2me | Theorems.Thm_GroundTheory_Global_relDiscr_tower
-- name    : GroundTheory.Global.relDiscr_tower
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:05.258557+00:00
-- url     : https://prove2.me/theorems/d5b56a5c-6f17-59b7-b7fe-f71b0ba39cc0
-- title:
--   Global: rel Discr tower
-- statement:
--   The Global construction uses the rel Discr tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L125-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L125-L130

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_Artin_RelativeDiscriminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open IsDedekindDomain NumberField Module
open GroundTheory GroundTheory.Global
variable (K M N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [Field N] [NumberField N] [Algebra K N] [Algebra M N] [IsScalarTower K M N]

theorem GroundTheory.Global.relDiscr_tower :
    relDiscr K N = relDiscr K M ^ finrank M N * Ideal.relNorm (𝓞 K) (relDiscr M N) := by sorry
