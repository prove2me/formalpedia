-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_laurent_ode_coeff
-- name    : GroundTheory.Global.Elliptic.laurent_ode_coeff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:51:30.703884+00:00
-- url     : https://prove2.me/theorems/a13b73ec-9563-4992-b36a-6b725ed2cf87
-- title:
--   Elliptic: laurent ode coeff
-- statement:
--   The Elliptic construction uses the laurent ode coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L145-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationEisenstein.lean#L145-L171

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

theorem GroundTheory.Global.Elliptic.laurent_ode_coeff (k : ℕ) :
    ((k + 2 : ℂ) * (k + 1)) * (iteratedDeriv (k + 2) ℘[L - (0 : ℂ)] 0 -
      6 * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℂ) * iteratedDeriv j ℘[L - (0 : ℂ)] 0 *
        iteratedDeriv (k - j) ℘[L - (0 : ℂ)] 0 + (if k = 0 then L.g₂ / 2 else 0)) =
      12 * iteratedDeriv (k + 2) ℘[L - (0 : ℂ)] 0 := by sorry
