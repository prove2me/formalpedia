-- Prove2me | Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_exists_diag
-- name    : GlobalTheory.TriangularIsometryBoundedPowers.exists_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:28.160549+00:00
-- url     : https://prove2.me/theorems/d9763ea1-b389-44f5-a9c4-d82a029413b3
-- title:
--   Triangular Isometry Bounded Powers: exists diag
-- statement:
--   The Triangular Isometry Bounded Powers construction uses the exists diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L64-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L64-L101

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

theorem GlobalTheory.TriangularIsometryBoundedPowers.exists_diag {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (hH : B.IsHermitian)
    (hB : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor B i ≠ 0) :
    ∃ (F : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ), F.BlockTriangular id ∧ F.det = 1 ∧
      (∀ i, μ i ≠ 0) ∧ Fᴴ * B * F = diagonal μ := by sorry
