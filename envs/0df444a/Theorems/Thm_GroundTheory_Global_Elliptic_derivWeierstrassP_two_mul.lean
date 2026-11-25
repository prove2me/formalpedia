-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_derivWeierstrassP_two_mul
-- name    : GroundTheory.Global.Elliptic.derivWeierstrassP_two_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:00:15.038013+00:00
-- url     : https://prove2.me/theorems/9a052872-9978-495d-a98a-9dfdf395fc35
-- title:
--   Elliptic: deriv Weierstrass P two mul
-- statement:
--   The Elliptic construction uses the deriv Weierstrass P two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L464-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L464-L480

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

theorem GroundTheory.Global.Elliptic.derivWeierstrassP_two_mul {w : ℂ} (hw : w ∉ L.lattice) (h2w : 2 * w ∉ L.lattice) :
    ℘'[L] (2 * w) = -(tangentSlope L w * (℘[L] (2 * w) - ℘[L] w) + ℘'[L] w) := by sorry
