-- Prove2me | Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_exists_col
-- name    : GlobalTheory.TriangularIsometryBoundedPowers.exists_col
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:24.814877+00:00
-- url     : https://prove2.me/theorems/6b17d520-d4f6-4109-bd29-ba6348028950
-- title:
--   Triangular Isometry Bounded Powers: exists col
-- statement:
--   The Triangular Isometry Bounded Powers construction uses the exists col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L30-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L30-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TriangularIsometryBoundedPowers
open Matrix

theorem GlobalTheory.TriangularIsometryBoundedPowers.exists_col {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    ∃ y : Fin n → ℂ, y j = 1 ∧ (∀ c, j < c → y c = 0) ∧
      ∀ a, a < j → ∑ c, B a c * y c = 0 := by sorry
