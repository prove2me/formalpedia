-- Prove2me | Theorems.Thm_GlobalTheory_torusAtExists
-- name    : GlobalTheory.torusAtExists
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:57:20.566595+00:00
-- url     : https://prove2.me/theorems/3c86789e-8d9d-4660-b044-0fa2acb500a0
-- title:
--   Global Theory: torus At Exists
-- statement:
--   The Global Theory construction uses the torus At Exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExists.lean#L103-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusSplitting/TorusAtExists.lean#L103-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_EqTopOfForallEmbAllMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_SumCMulImHermCEqSignMulTrace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExistsOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TorusAtExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open NumberField

theorem GlobalTheory.torusAtExists : _root_.ReciprocityTheory.ChartRestriction.G.I2.TorusAtExistsStatement := by sorry
