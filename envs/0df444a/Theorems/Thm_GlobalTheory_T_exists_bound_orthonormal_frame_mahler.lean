-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_bound_orthonormal_frame_mahler
-- name    : GlobalTheory.T.exists_bound_orthonormal_frame_mahler
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:33:27.829802+00:00
-- url     : https://prove2.me/theorems/880e067c-3cd5-5cc5-a4e6-30913ad4c738
-- title:
--   T: exists bound orthonormal frame mahler
-- statement:
--   The T construction uses the exists bound orthonormal frame mahler property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBoundOrthonormalFrameMahlerStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBoundOrthonormalFrameMahlerStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBoundOrthonormalFrameMahler
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBoundOrthonormalFrameMahlerStatement
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

theorem GlobalTheory.T.exists_bound_orthonormal_frame_mahler : (∀ (r : ℕ) (X : Data E r) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x, IsOrth X x → ε ≤ X.la1 x → ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ a b, ‖lact γ x τ a b‖ ≤ R) := by sorry
