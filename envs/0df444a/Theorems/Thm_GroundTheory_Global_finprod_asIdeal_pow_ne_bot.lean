-- Prove2me | Theorems.Thm_GroundTheory_Global_finprod_asIdeal_pow_ne_bot
-- name    : GroundTheory.Global.finprod_asIdeal_pow_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:43.734453+00:00
-- url     : https://prove2.me/theorems/2cf83043-8f9a-4a8b-95c9-7c9d6e244149
-- title:
--   Global: finprod as Ideal pow ne bot
-- statement:
--   The Global construction uses the finprod as Ideal pow ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L33-L36

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R]

theorem GroundTheory.Global.finprod_asIdeal_pow_ne_bot (a : HeightOneSpectrum R → ℕ) :
    (∏ᶠ v : HeightOneSpectrum R, v.asIdeal ^ a v) ≠ ⊥ := by sorry
