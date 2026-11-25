-- Prove2me | Theorems.Thm_GroundTheory_Global_coe_derivative_reverse_charpoly
-- name    : GroundTheory.Global.coe_derivative_reverse_charpoly
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:08.324906+00:00
-- url     : https://prove2.me/theorems/ef3b9506-1ee1-4fd1-bf95-fa20cc07e5f7
-- title:
--   Global: coe derivative reverse charpoly
-- statement:
--   The Global construction uses the coe derivative reverse charpoly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/LogCharpoly.lean#L132-L141

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

theorem GroundTheory.Global.coe_derivative_reverse_charpoly (A : Module.End k W) :
    ((derivative A.charpoly.reverse : k[X]) : PowerSeries k) =
      -(A.charpoly.reverse : PowerSeries k) *
        PowerSeries.mk fun m => LinearMap.trace k W (A ^ (m + 1)) := by sorry
