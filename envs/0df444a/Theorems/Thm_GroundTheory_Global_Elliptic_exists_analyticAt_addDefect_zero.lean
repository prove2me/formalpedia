-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_exists_analyticAt_addDefect_zero
-- name    : GroundTheory.Global.Elliptic.exists_analyticAt_addDefect_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:48:20.044809+00:00
-- url     : https://prove2.me/theorems/a0e5a8eb-2553-4db9-bef9-0d9e5ecc2932
-- title:
--   Elliptic: exists analytic At add Defect zero
-- statement:
--   The Elliptic construction uses the exists analytic At add Defect zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L180-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L180-L203

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

theorem GroundTheory.Global.Elliptic.exists_analyticAt_addDefect_zero {w : ℂ} (hw : w ∉ L.lattice) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ H 0 = 0 ∧ addDefect L w =ᶠ[𝓝[≠] 0] H := by sorry
