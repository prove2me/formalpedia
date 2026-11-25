-- Prove2me | Theorems.Thm_GroundTheory_Global_SemiLocal_valued_algebraMap_int_lt_one_iff
-- name    : GroundTheory.Global.SemiLocal.valued_algebraMap_int_lt_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:39:18.847041+00:00
-- url     : https://prove2.me/theorems/467e47a1-31a1-4455-bef0-148951f1b4e2
-- title:
--   Semi Local: valued algebra Map int lt one iff
-- statement:
--   The Semi Local construction uses the valued algebra Map int lt one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/LocalDegree.lean#L28-L31

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

theorem GroundTheory.Global.SemiLocal.valued_algebraMap_int_lt_one_iff (b : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (u.adicCompletion F) b) < 1 ↔ b ∈ u.asIdeal := by sorry
