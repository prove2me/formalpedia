-- Prove2me | Theorems.Thm_GroundTheory_Global_pow_mul_mem_factoredIdeals_insert
-- name    : GroundTheory.Global.pow_mul_mem_factoredIdeals_insert
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:03:18.360199+00:00
-- url     : https://prove2.me/theorems/f9109e75-5b88-4a63-b44a-8d920e5baa99
-- title:
--   Global: pow mul mem factored Ideals insert
-- statement:
--   The Global construction uses the pow mul mem factored Ideals insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L46-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L46-L57

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

theorem GroundTheory.Global.pow_mul_mem_factoredIdeals_insert [DecidableEq (HeightOneSpectrum R)]
    {S : Finset (HeightOneSpectrum R)}
    {v : HeightOneSpectrum R} {I : Ideal R} (hI : I ∈ factoredIdeals S) (k : ℕ) :
    v.asIdeal ^ k * I ∈ factoredIdeals (insert v S) := by sorry
