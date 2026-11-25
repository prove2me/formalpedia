-- Prove2me | Theorems.Thm_GroundTheory_Global_hasProd_euler
-- name    : GroundTheory.Global.hasProd_euler
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:00:11.260437+00:00
-- url     : https://prove2.me/theorems/20d66451-8cbb-5307-9542-ee6943da0b63
-- title:
--   Global: has Prod euler
-- statement:
--   The Global construction uses the has Prod euler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L173-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L173-L191

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
variable {R : Type*} [CommRing R] [IsDedekindDomain R] (g : Ideal R →* ℂ)

theorem GroundTheory.Global.hasProd_euler (hsum : Summable fun I ↦ ‖g I‖) (h0 : g ⊥ = 0) :
    HasProd (fun v : HeightOneSpectrum R ↦ (1 - g v.asIdeal)⁻¹) (∑' I, g I) := by sorry
