-- Prove2me | Theorems.Thm_GroundTheory_Global_asIdeal_pow_eq_one_iff
-- name    : GroundTheory.Global.asIdeal_pow_eq_one_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:28.18151+00:00
-- url     : https://prove2.me/theorems/2f4c5345-19f1-4678-8e19-86a7a86318a5
-- title:
--   Global: as Ideal pow eq one iff
-- statement:
--   The Global construction uses the as Ideal pow eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L17-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L17-L25

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

theorem GroundTheory.Global.asIdeal_pow_eq_one_iff (v : HeightOneSpectrum R) {k : ℕ} : v.asIdeal ^ k = 1 ↔ k = 0 := by sorry
