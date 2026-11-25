-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_two_mul
-- name    : GroundTheory.Global.Elliptic.weierstrassP_two_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:09.285799+00:00
-- url     : https://prove2.me/theorems/b8573b84-0a00-52da-8075-7f77c65c3d9b
-- title:
--   Elliptic: weierstrass P two mul
-- statement:
--   The Elliptic construction uses the weierstrass P two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L449-L462
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L449-L462

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

theorem GroundTheory.Global.Elliptic.weierstrassP_two_mul {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘[L] (2 * w) = tangentSlope L w ^ 2 / 4 - 2 * ℘[L] w := by sorry
