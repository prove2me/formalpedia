-- Prove2me | Theorems.Thm_GroundTheory_Global_isCoprime_asIdeal_iff
-- name    : GroundTheory.Global.isCoprime_asIdeal_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:00:09.378477+00:00
-- url     : https://prove2.me/theorems/2da455f6-abdc-5b53-b620-71c1f5fc27fc
-- title:
--   Global: is Coprime as Ideal iff
-- statement:
--   The Global construction uses the is Coprime as Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L241-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L241-L248

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SummableAbsNormRpowInv
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeLFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero FractionalIdeal Function Ideal
open scoped NumberField.AdeleRing nonZeroDivisors
open GroundTheory GroundTheory.Global
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.isCoprime_asIdeal_iff (v : HeightOneSpectrum (𝓞 K)) (𝔪 : Ideal (𝓞 K)) :
    IsCoprime v.asIdeal 𝔪 ↔ ¬ v.asIdeal ∣ 𝔪 := by sorry
