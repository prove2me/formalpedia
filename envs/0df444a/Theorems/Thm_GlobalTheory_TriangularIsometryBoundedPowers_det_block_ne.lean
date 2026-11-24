-- Prove2me | Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_det_block_ne
-- name    : GlobalTheory.TriangularIsometryBoundedPowers.det_block_ne
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:15.468858+00:00
-- url     : https://prove2.me/theorems/61b53f08-c709-47cc-89b8-360149c14c44
-- title:
--   Triangular Isometry Bounded Powers: det block ne
-- statement:
--   The Triangular Isometry Bounded Powers construction uses the det block ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L10-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L10-L28

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

theorem GlobalTheory.TriangularIsometryBoundedPowers.det_block_ne {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) (j : Fin n) :
    (B.submatrix (Subtype.val : {c : Fin n // c < j} → Fin n)
      (Subtype.val : {c : Fin n // c < j} → Fin n)).det ≠ 0 := by sorry
