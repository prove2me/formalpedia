-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_laurent_ode
-- name    : GroundTheory.Global.Elliptic.laurent_ode
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:51:34.436581+00:00
-- url     : https://prove2.me/theorems/4c9fa204-1919-4ca3-b7d0-39dd32d58db2
-- title:
--   Elliptic: laurent ode
-- statement:
--   The Elliptic construction uses the laurent ode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L108-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L108-L137

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.laurent_ode :
    (fun z ↦ z ^ 2 * (deriv (deriv ℘[L - (0 : ℂ)]) z -
      6 * (℘[L - (0 : ℂ)] z * ℘[L - (0 : ℂ)] z) + L.g₂ / 2)) =ᶠ[𝓝 0]
      (fun z ↦ 12 * ℘[L - (0 : ℂ)] z) := by sorry
