-- Prove2me | Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_diag_of_isometry
-- name    : GlobalTheory.TriangularIsometryBoundedPowers.diag_of_isometry
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:13.468376+00:00
-- url     : https://prove2.me/theorems/3a264b37-64d8-46a6-8c0a-c9d59d98d338
-- title:
--   Triangular Isometry Bounded Powers: diag of isometry
-- statement:
--   The Triangular Isometry Bounded Powers construction uses the diag of isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L103-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L103-L148

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

theorem GlobalTheory.TriangularIsometryBoundedPowers.diag_of_isometry {n : ℕ} (d : Matrix (Fin n) (Fin n) ℂ) (μ : Fin n → ℂ)
    (hd : d.BlockTriangular id) (hμ : ∀ i, μ i ≠ 0)
    (h : dᴴ * diagonal μ * d = diagonal μ) :
    ∃ l : Fin n → ℂ, d = diagonal l ∧ ∀ i, ‖l i‖ = 1 := by sorry
