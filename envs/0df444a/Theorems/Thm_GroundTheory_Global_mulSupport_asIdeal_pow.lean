-- Prove2me | Theorems.Thm_GroundTheory_Global_mulSupport_asIdeal_pow
-- name    : GroundTheory.Global.mulSupport_asIdeal_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:45.177745+00:00
-- url     : https://prove2.me/theorems/78a61356-2843-4faf-9dfa-0cdccee74c8e
-- title:
--   Global: mul Support as Ideal pow
-- statement:
--   The Global construction uses the mul Support as Ideal pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L28-L31

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
omit [IsDedekindDomain R]

theorem GroundTheory.Global.mulSupport_asIdeal_pow (a : HeightOneSpectrum R → ℕ) :
    mulSupport (fun v : HeightOneSpectrum R ↦ v.asIdeal ^ a v) = support a := by sorry
