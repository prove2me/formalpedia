-- Prove2me | Theorems.Thm_GlobalTheory_GamFree_pow_bounded
-- name    : GlobalTheory.GamFree.pow_bounded
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T13:49:52.344278+00:00
-- url     : https://prove2.me/theorems/2a80d152-b0aa-4e6c-9746-da376684fe71
-- title:
--   Gam Free: pow bounded
-- statement:
--   The Gam Free construction uses the pow bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOfFinOrderOfBounded.lean#L14-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsIntMulIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_BoundedPowOfTriangularIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOfFinOrderOfBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.GamFree

theorem GlobalTheory.GamFree.pow_bounded {n : ℕ} (g x b A : Matrix (Fin n) (Fin n) ℂ) (hx : x.det ≠ 0)
    (hb : b.BlockTriangular id) (hA : A.IsHermitian) (hm : ∀ i, FD.lminor A i ≠ 0)
    (hg : g * x = x * b) (hbA : bᵀ * A * b.map (starRingEnd ℂ) = A) :
    ∃ R : ℝ, ∀ (k : ℕ) (i j : Fin n), ‖(g ^ k) i j‖ ≤ R := by sorry
