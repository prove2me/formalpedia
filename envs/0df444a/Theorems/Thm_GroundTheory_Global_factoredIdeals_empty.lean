-- Prove2me | Theorems.Thm_GroundTheory_Global_factoredIdeals_empty
-- name    : GroundTheory.Global.factoredIdeals_empty
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:06:17.344114+00:00
-- url     : https://prove2.me/theorems/9cf8c3a7-7265-4c96-9f0a-698e3a067a46
-- title:
--   Global: factored Ideals empty
-- statement:
--   The Global construction uses the factored Ideals empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L34-L44

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

theorem GroundTheory.Global.factoredIdeals_empty : factoredIdeals (∅ : Finset (HeightOneSpectrum R)) = {⊤} := by sorry
