-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_weierstrassP_add_of_two_mul_notMem
-- name    : GroundTheory.Global.Elliptic.weierstrassP_add_of_two_mul_notMem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:49:10.006353+00:00
-- url     : https://prove2.me/theorems/0c4495ef-26f3-5477-a47a-51c9f47672ca
-- title:
--   Elliptic: weierstrass P add of two mul not Mem
-- statement:
--   The Elliptic construction uses the weierstrass P add of two mul not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L283-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L283-L325

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

theorem GroundTheory.Global.Elliptic.weierstrassP_add_of_two_mul_notMem {z w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) (hz : z ∉ L.lattice) (hzw : z - w ∉ L.lattice)
    (hzw' : z + w ∉ L.lattice) :
    ℘[L] (z + w) = chordSlope L z w ^ 2 / 4 - ℘[L] z - ℘[L] w := by sorry
