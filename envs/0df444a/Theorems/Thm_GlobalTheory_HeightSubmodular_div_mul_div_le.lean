-- Prove2me | Theorems.Thm_GlobalTheory_HeightSubmodular_div_mul_div_le
-- name    : GlobalTheory.HeightSubmodular.div_mul_div_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:17:49.333533+00:00
-- url     : https://prove2.me/theorems/bb5c8608-6b5a-4c3d-9a59-5ada3676764f
-- title:
--   Height Submodular: div mul div le
-- statement:
--   The Height Submodular construction uses the div mul div le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetReNonneg.lean#L20-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetReNonneg.lean#L20-L31

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisAdaptedMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexIntegralSpanSupermultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetReNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.HeightSubmodular

theorem GlobalTheory.HeightSubmodular.div_mul_div_le {p q p' q' : ℝ} {i j i' j' : ℕ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p * q ≤ p' * q') (hi : i' ≠ 0) (hj : j' ≠ 0) (hij : i' * j' ≤ i * j) :
    p / i * (q / j) ≤ p' / i' * (q' / j') := by sorry
