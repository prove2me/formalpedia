-- Prove2me | Theorems.Thm_GroundTheory_Global_RayClassGroup_finite
-- name    : GroundTheory.Global.RayClassGroup.finite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:03:58.137483+00:00
-- url     : https://prove2.me/theorems/38136e5c-9174-4169-8fed-c93b2bc0132e
-- title:
--   Ray Class Group: finite
-- statement:
--   The Ray Class Group construction uses the finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L233-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeCharRayClass.lean#L233-L268

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
open IdeleGroup

theorem GroundTheory.Global.RayClassGroup.finite {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) : Finite (RayClassGroup K 𝔪) := by sorry
