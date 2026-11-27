-- Prove2me | Theorems.Thm_GroundTheory_Global_relDiscr_ne_bot
-- name    : GroundTheory.Global.relDiscr_ne_bot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:56:05.574076+00:00
-- url     : https://prove2.me/theorems/149be6bc-3270-5e42-87c2-da0c86de6d58
-- title:
--   Global: rel Discr ne bot
-- statement:
--   The Global construction uses the rel Discr ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/RelativeDiscriminant.lean#L18-L20

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
variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem GroundTheory.Global.relDiscr_ne_bot : relDiscr K M ≠ ⊥ := by sorry
