-- Prove2me | Theorems.Thm_GlobalTheory_ae_eval_circleMap_ne_zero
-- name    : GlobalTheory.ae_eval_circleMap_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T02:56:16.932928+00:00
-- url     : https://prove2.me/theorems/f9164174-8813-4276-aefe-a35ae2c86ee7
-- title:
--   Global Theory: ae eval circle Map ne zero
-- statement:
--   The Global Theory construction uses the ae eval circle Map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AeEvalCircleMapNeZero.lean#L13-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AeEvalCircleMapNeZero.lean#L13-L73

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CastAddNeNatAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralLogNormLeHalfLogIntegralSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AeEvalCircleMapNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.ae_eval_circleMap_ne_zero : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f ≠ 0 := by sorry
