-- Prove2me | Theorems.Thm_GroundTheory_Global_HeckeCharacter_analyticOnNhd_LFunction
-- name    : GroundTheory.Global.HeckeCharacter.analyticOnNhd_LFunction
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:05:22.795449+00:00
-- url     : https://prove2.me/theorems/06ff69e1-7847-5899-aa0b-f32d5cfef642
-- title:
--   Hecke Character: analytic On Nhd LFunction
-- statement:
--   The Hecke Character construction uses the analytic On Nhd LFunction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L431-L433
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/HeckeLFunction.lean#L431-L433

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
open GroundTheory.Global.HeckeCharacter
variable {K : Type*} [Field K] [NumberField K] (χ : HeckeCharacter K)

theorem GroundTheory.Global.HeckeCharacter.analyticOnNhd_LFunction : AnalyticOnNhd ℂ χ.LFunction {s | 1 < s.re} := by sorry
