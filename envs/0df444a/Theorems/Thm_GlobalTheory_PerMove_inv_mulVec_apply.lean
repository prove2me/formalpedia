-- Prove2me | Theorems.Thm_GlobalTheory_PerMove_inv_mulVec_apply
-- name    : GlobalTheory.PerMove.inv_mulVec_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:41:11.488806+00:00
-- url     : https://prove2.me/theorems/edeb0ff5-4151-45ef-9b93-97aa7a80173b
-- title:
--   Per Move: inv mul Vec apply
-- statement:
--   The Per Move construction uses the inv mul Vec apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetOfTriangular.lean#L26-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_DetSubUpper
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetOfTriangular
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
open GlobalTheory GlobalTheory.PerMove
open scoped ComplexConjugate
open NumberField Matrix
open scoped nonZeroDivisors
open scoped ComplexConjugate

theorem GlobalTheory.PerMove.inv_mulVec_apply {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) (a : Fin r) :
    (A⁻¹ *ᵥ w) a = (A.det)⁻¹ * (A.updateCol a w).det := by sorry
