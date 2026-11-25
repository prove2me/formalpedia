-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_derivAdd_algebra
-- name    : GroundTheory.Global.Elliptic.derivAdd_algebra
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:49:00.784971+00:00
-- url     : https://prove2.me/theorems/3dc22e76-2c7b-459f-b2ef-13ce630bc44c
-- title:
--   Elliptic: deriv Add algebra
-- statement:
--   The Elliptic construction uses the deriv Add algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L371-L385
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L371-L385

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticDegree
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
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
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}

theorem GroundTheory.Global.Elliptic.derivAdd_algebra (x₁ x₂ y₁ y₂ g₂ g₃ : ℂ) (hD : x₁ - x₂ ≠ 0)
    (E₁ : y₁ ^ 2 = 4 * x₁ ^ 3 - g₂ * x₁ - g₃) (E₂ : y₂ ^ 2 = 4 * x₂ ^ 3 - g₂ * x₂ - g₃) :
    2 * ((y₁ - y₂) / (x₁ - x₂)) *
        (((6 * x₁ ^ 2 - g₂ / 2) * (x₁ - x₂) - (y₁ - y₂) * y₁) / (x₁ - x₂) ^ 2) / 4 - y₁ =
      -((y₁ - y₂) / (x₁ - x₂) * (((y₁ - y₂) / (x₁ - x₂)) ^ 2 / 4 - x₁ - x₂ - x₁) + y₁) := by sorry
