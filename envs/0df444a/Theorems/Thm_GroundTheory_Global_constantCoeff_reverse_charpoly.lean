-- Prove2me | Theorems.Thm_GroundTheory_Global_constantCoeff_reverse_charpoly
-- name    : GroundTheory.Global.constantCoeff_reverse_charpoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:16.149761+00:00
-- url     : https://prove2.me/theorems/26681481-0cb5-49fa-8a1b-4829df607bef
-- title:
--   Global: constant Coeff reverse charpoly
-- statement:
--   The Global construction uses the constant Coeff reverse charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L127-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L127-L130

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open GroundTheory GroundTheory.Global
variable {k W W' : Type*} [Field k] [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  [AddCommGroup W'] [Module k W'] [FiniteDimensional k W']

theorem GroundTheory.Global.constantCoeff_reverse_charpoly (A : Module.End k W) :
    PowerSeries.constantCoeff (A.charpoly.reverse : PowerSeries k) = 1 := by sorry
