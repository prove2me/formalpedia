-- Prove2me | Theorems.Thm_GlobalTheory_FinCovol_isCompact_orth_bounded
-- name    : GlobalTheory.FinCovol.isCompact_orth_bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:31.793711+00:00
-- url     : https://prove2.me/theorems/8ee131c3-7322-4e51-9a7b-2556885ab64f
-- title:
--   Fin Covol: is Compact orth bounded
-- statement:
--   The Fin Covol construction uses the is Compact orth bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsCompactOrthBounded.lean#L12-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/IsCompactOrthBounded.lean#L12-L36

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsCompactOrthBounded
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
open GlobalTheory GlobalTheory.FinCovol
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FinCovol.isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by sorry
