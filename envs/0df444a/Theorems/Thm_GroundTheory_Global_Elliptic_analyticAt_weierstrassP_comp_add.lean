-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_weierstrassP_comp_add
-- name    : GroundTheory.Global.Elliptic.analyticAt_weierstrassP_comp_add
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:08:11.235047+00:00
-- url     : https://prove2.me/theorems/1a4ea412-ccb7-4ae6-8fd1-ebd313965ef0
-- title:
--   Elliptic: analytic At weierstrass P comp add
-- statement:
--   The Elliptic construction uses the analytic At weierstrass P comp add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L129-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L129-L131

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

theorem GroundTheory.Global.Elliptic.analyticAt_weierstrassP_comp_add {x w : ℂ} (h : x + w ∉ L.lattice) :
    AnalyticAt ℂ (fun z ↦ ℘[L] (z + w)) x := by sorry
