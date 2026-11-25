-- Prove2me | Theorems.Thm_GlobalTheory_normDiscrete_mem_vRing_iff
-- name    : GlobalTheory.normDiscrete_mem_vRing_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:19:40.8148+00:00
-- url     : https://prove2.me/theorems/1d98315c-cc5a-42f4-949a-471e57e62a0d
-- title:
--   Global Theory: norm Discrete mem v Ring iff
-- statement:
--   The Global Theory construction uses the norm Discrete mem v Ring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/ExistsCompleteDiscreteValuationRingOfIsNormDiscr.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/ExistsCompleteDiscreteValuationRingOfIsNormDiscr.lean#L16-L16

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

theorem GlobalTheory.normDiscrete_mem_vRing_iff (x : Ω) : x ∈ vRing v ↔ 0 ≤ v x := by sorry
