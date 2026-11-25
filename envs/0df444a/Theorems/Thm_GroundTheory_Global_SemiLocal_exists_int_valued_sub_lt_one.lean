-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_exists_int_valued_sub_lt_one
-- name    : GroundTheory.Global.SemiLocal.exists_int_valued_sub_lt_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:31.716015+00:00
-- url     : https://prove2.me/theorems/0302f59f-633e-4f1e-904f-31d5cd89e662
-- title:
--   Semi Local: exists int valued sub lt one
-- statement:
--   The Semi Local construction uses the exists int valued sub lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L38-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L38-L68

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_ContinuousCompletionMap
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_LocalDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField WithZero
noncomputable section
open GroundTheory.Global.SemiLocal
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem GroundTheory.Global.SemiLocal.exists_int_valued_sub_lt_one (d : u.adicCompletion F) (hd : Valued.v d ≤ 1) :
    ∃ r : 𝓞 F, Valued.v (d - algebraMap (𝓞 F) (u.adicCompletion F) r) < 1 := by sorry
