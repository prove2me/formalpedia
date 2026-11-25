-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_ord_eq_zero_of_mem_unitsLevel
-- name    : GroundTheory.Global.IdeleGroup.ord_eq_zero_of_mem_unitsLevel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:50:12.813398+00:00
-- url     : https://prove2.me/theorems/f66351be-012c-4554-80e9-8cb8c5637980
-- title:
--   Idele Group: ord eq zero of mem units Level
-- statement:
--   The Idele Group construction uses the ord eq zero of mem units Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L75-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeChar.lean#L75-L77

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

theorem GroundTheory.Global.IdeleGroup.ord_eq_zero_of_mem_unitsLevel {v : HeightOneSpectrum (𝓞 K)} {x : IdeleGroup K} {n : ℕ}
    (h : finiteProj v x ∈ unitsLevel v n) : ord v x = 0 := by sorry
