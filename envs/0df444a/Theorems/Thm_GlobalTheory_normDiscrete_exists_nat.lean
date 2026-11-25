-- Prove2me | Theorems.Thm_GlobalTheory_normDiscrete_exists_nat
-- name    : GlobalTheory.normDiscrete_exists_nat
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:21:28.419914+00:00
-- url     : https://prove2.me/theorems/0ca9e08e-7697-476e-8f34-d87eb2de22c3
-- title:
--   Global Theory: norm Discrete exists nat
-- statement:
--   The Global Theory construction uses the norm Discrete exists nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/ExistsCompleteDiscreteValuationRingOfIsNormDiscr.lean#L61-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AlgebraicCurves/ExistsCompleteDiscreteValuationRingOfIsNormDiscr.lean#L61-L67

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

theorem GlobalTheory.normDiscrete_exists_nat (hv : IsNormDiscrete v) (x : vRing v) (hx : x ≠ 0) :
    ∃ n : ℕ, v (x : Ω) = ((n : ℤ) : WithTop ℤ) := by sorry
