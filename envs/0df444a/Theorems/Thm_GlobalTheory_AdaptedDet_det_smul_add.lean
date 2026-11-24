-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedDet_det_smul_add
-- name    : GlobalTheory.AdaptedDet.det_smul_add
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:54:39.570044+00:00
-- url     : https://prove2.me/theorems/0c501717-ddf0-44a2-83ea-5dcbf1325805
-- title:
--   Adapted Det: det smul add
-- statement:
--   The Adapted Det construction uses the det smul add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L31-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/CmUnitPowFourIdempotentModEight.lean#L31-L53

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet

theorem GlobalTheory.AdaptedDet.det_smul_add {K : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (c a : K) (hc : c ≠ 0) :
    (c • A + a • (1 : Matrix (Fin r) (Fin r) K)).det =
      (A.charpoly.roots.map fun μ => c * μ + a).prod := by sorry
