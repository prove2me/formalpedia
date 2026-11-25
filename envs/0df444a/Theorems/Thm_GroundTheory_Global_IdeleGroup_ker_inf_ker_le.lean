-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ker_inf_ker_le
-- name    : GroundTheory.Global.IdeleGroup.ker_inf_ker_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:01:22.701433+00:00
-- url     : https://prove2.me/theorems/63fb3799-1e39-5f9a-8d95-ac51b309ce74
-- title:
--   Idele Group: ker inf ker le
-- statement:
--   The Idele Group construction uses the ker inf ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L212-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L212-L223

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function Complex
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.ker_inf_ker_le (𝔪 : Ideal (𝓞 K)) :
    (standardOpenInfiniteHom (K := K)).ker ⊓ (standardOpenFiniteHom 𝔪).ker ≤
      ((idealLevel 𝔪).map ofFinite ⊔ (infinitePositive K).map ofInfinite).subgroupOf
        (standardOpenSubgroup K) := by sorry
