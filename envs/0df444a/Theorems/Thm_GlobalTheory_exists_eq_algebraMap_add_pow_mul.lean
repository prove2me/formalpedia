-- Prove2me | Theorems.Thm_GlobalTheory_exists_eq_algebraMap_add_pow_mul
-- name    : GlobalTheory.exists_eq_algebraMap_add_pow_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:37.513663+00:00
-- url     : https://prove2.me/theorems/ec140295-e86d-4ead-b8e3-d00cf1da286b
-- title:
--   Global Theory: exists eq algebra Map add pow mul
-- statement:
--   The Global Theory construction uses the exists eq algebra Map add pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L92-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/IsIntegralIffMemSpanOneTmulIntegralClosure.lean#L92-L114

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsIntegralIffMemSpanOneTmulIntegralClosure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open Polynomial
open GlobalTheory

theorem GlobalTheory.exists_eq_algebraMap_add_pow_mul {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')] {ϖ : R}
    (hϖ : IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' ϖ})
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R'))) (n : ℕ)
    (r' : R') : ∃ (r : R) (s : R'), r' = algebraMap R R' r + algebraMap R R' ϖ ^ n * s := by sorry
