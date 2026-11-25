-- Prove2me | Theorems.Thm_GroundTheory_Global_Modulus_exponent_eq_zero_iff
-- name    : GroundTheory.Global.Modulus.exponent_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:14:12.846579+00:00
-- url     : https://prove2.me/theorems/0b9a6c5c-4256-45e8-9291-1ce36b5053e2
-- title:
--   Modulus: exponent eq zero iff
-- statement:
--   The Modulus construction uses the exponent eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L64-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L64-L66

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

theorem GroundTheory.Global.Modulus.exponent_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) :
    𝔪.exponent v = 0 ↔ ¬ v.asIdeal ∣ 𝔪.ideal := by sorry
