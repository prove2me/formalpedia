-- Prove2me | Theorems.Thm_GroundTheory_Global_Elliptic_neg_one_le_meromorphicOrderAt_addDefect_neg
-- name    : GroundTheory.Global.Elliptic.neg_one_le_meromorphicOrderAt_addDefect_neg
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:49:58.512014+00:00
-- url     : https://prove2.me/theorems/1e954aa1-4b9c-4b7e-842f-722ea3d19378
-- title:
--   Elliptic: neg one le meromorphic Order At add Defect neg
-- statement:
--   The Elliptic construction uses the neg one le meromorphic Order At add Defect neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L224-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/UniformizationAddition.lean#L224-L281

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

theorem GroundTheory.Global.Elliptic.neg_one_le_meromorphicOrderAt_addDefect_neg {w : ℂ} (hw : w ∉ L.lattice)
    (h2w : 2 * w ∉ L.lattice) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (addDefect L w) (-w) := by sorry
