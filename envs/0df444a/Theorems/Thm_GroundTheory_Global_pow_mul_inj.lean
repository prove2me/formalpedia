-- Prove2me | Theorems.Thm_GroundTheory_Global_pow_mul_inj
-- name    : GroundTheory.Global.pow_mul_inj
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T08:01:23.382831+00:00
-- url     : https://prove2.me/theorems/26eff231-9e0f-5235-ba11-63a43bdcf58b
-- title:
--   Global: pow mul inj
-- statement:
--   The Global construction uses the pow mul inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L59-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L59-L75

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem GroundTheory.Global.pow_mul_inj {v : HeightOneSpectrum R} {k j : ℕ} {I J : Ideal R}
    (hI : ¬ v.asIdeal ∣ I) (hJ : ¬ v.asIdeal ∣ J) (h : v.asIdeal ^ k * I = v.asIdeal ^ j * J) :
    k = j ∧ I = J := by sorry
