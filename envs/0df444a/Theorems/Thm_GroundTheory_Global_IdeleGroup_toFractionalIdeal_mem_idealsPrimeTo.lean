-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_toFractionalIdeal_mem_idealsPrimeTo
-- name    : GroundTheory.Global.IdeleGroup.toFractionalIdeal_mem_idealsPrimeTo
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:06.578542+00:00
-- url     : https://prove2.me/theorems/19a04d3d-1a12-5f8f-85cb-82e6f22dca58
-- title:
--   Idele Group: to Fractional Ideal mem ideals Prime To
-- statement:
--   The Idele Group construction uses the to Fractional Ideal mem ideals Prime To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L109-L113

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
  FractionalIdeal Function
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.toFractionalIdeal_mem_idealsPrimeTo {𝔪 : Ideal (𝓞 K)} {x : IdeleGroup K}
    (hx : x ∈ primeToLevel 𝔪) : toFractionalIdeal x ∈ idealsPrimeTo 𝔪 := by sorry
