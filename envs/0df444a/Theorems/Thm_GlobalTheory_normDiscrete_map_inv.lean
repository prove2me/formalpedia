-- Prove2me | Theorems.Thm_GlobalTheory_normDiscrete_map_inv
-- name    : GlobalTheory.normDiscrete_map_inv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:24:49.487808+00:00
-- url     : https://prove2.me/theorems/8e27a9bf-bdcf-4cfb-9107-9f7077d23232
-- title:
--   Global Theory: norm Discrete map inv
-- statement:
--   The Global Theory construction uses the norm Discrete map inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/ExistsCompleteDiscreteValuationRingOfIsNormDiscr.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/ExistsCompleteDiscreteValuationRingOfIsNormDiscr.lean#L18-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_ExistsCompleteDiscreteValuationRingOfIsNormDiscr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing
open scoped TensorProduct
open GlobalTheory
variable {Ω : Type*} [Field Ω] {v : AddValuation Ω (WithTop ℤ)}

theorem GlobalTheory.normDiscrete_map_inv {x : Ω} {n : ℤ} (hx : v x = (n : WithTop ℤ)) :
    v x⁻¹ = ((-n : ℤ) : WithTop ℤ) := by sorry
