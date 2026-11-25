-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_one_le_exponent_iff
-- name    : GroundTheory.Global.Modulus.one_le_exponent_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:48.733364+00:00
-- url     : https://prove2.me/theorems/220305ef-8104-4b89-91e3-4d4df25f9daf
-- title:
--   Modulus: one le exponent iff
-- statement:
--   The Modulus construction uses the one le exponent iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L69-L71

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
omit [NumberField K]

theorem GroundTheory.Global.Modulus.one_le_exponent_iff (v : HeightOneSpectrum (𝓞 K)) :
    1 ≤ 𝔪.exponent v ↔ v.asIdeal ∣ 𝔪.ideal := by sorry
