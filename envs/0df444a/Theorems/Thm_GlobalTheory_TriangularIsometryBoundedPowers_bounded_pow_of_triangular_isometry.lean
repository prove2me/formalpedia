-- Prove2me | Theorems.Thm_GlobalTheory_TriangularIsometryBoundedPowers_bounded_pow_of_triangular_isometry
-- name    : GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:12:35.266514+00:00
-- url     : https://prove2.me/theorems/0d0422c2-e288-485f-9734-4a7afbf9b265
-- title:
--   Triangular Isometry Bounded Powers: bounded pow of triangular isometry
-- statement:
--   The Triangular Isometry Bounded Powers construction uses the bounded pow of triangular isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L181-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/BoundedPowOfTriangularIsometry.lean#L181-L213

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

theorem GlobalTheory.TriangularIsometryBoundedPowers.bounded_pow_of_triangular_isometry {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ)
    (hx : Matrix.det x ≠ (0 : ℂ)) (hb : Matrix.BlockTriangular b id) (hA : Matrix.IsHermitian A)
    (hm : ∀ i : Fin (n + 1), ReciprocityTheory.ChartRestriction.G.FD.lminor A i ≠ (0 : ℂ)) (hg : g * x = x * b)
    (hiso : Matrix.transpose b * A * Matrix.map b (⇑(starRingEnd ℂ) : ℂ → ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by sorry
