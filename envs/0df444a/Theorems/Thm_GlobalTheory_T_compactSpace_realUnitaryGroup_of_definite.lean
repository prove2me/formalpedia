-- Prove2me | Theorems.Thm_GlobalTheory_T_compactSpace_realUnitaryGroup_of_definite
-- name    : GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:30:25.054181+00:00
-- url     : https://prove2.me/theorems/bedeff3b-19b9-4c56-ab5b-58ee7543e29f
-- title:
--   T: compact Space real Unitary Group of definite
-- statement:
--   The T construction uses the compact Space real Unitary Group of definite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactSpaceRealUnitaryGroupOfDefiniteStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CompactSpaceRealUnitaryGroupOfDefiniteStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CompactSpaceRealUnitaryGroupOfDefiniteStatement
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

theorem GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by sorry
