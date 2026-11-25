-- Prove2me | Theorems.Thm_GlobalTheory_OrthFrameMahler_continuousOn_rmul_self
-- name    : GlobalTheory.OrthFrameMahler.continuousOn_rmul_self
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:18:36.561776+00:00
-- url     : https://prove2.me/theorems/0749ee68-11f6-41d4-949f-8d075ba56530
-- title:
--   Orth Frame Mahler: continuous On rmul self
-- statement:
--   The Orth Frame Mahler construction uses the continuous On rmul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBoundOrthonormalFrameMahler.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBoundOrthonormalFrameMahler.lean#L18-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsContinuousGramSchmidt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MahlerCompactness
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_UpperTriangularPreservesDiagonalIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBoundOrthonormalFrameMahler
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
open GlobalTheory GlobalTheory.OrthFrameMahler
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.OrthFrameMahler.continuousOn_rmul_self {Ψ : Finset (E →+* ℂ)} {r : ℕ} {β : Frame Ψ r → Frame Ψ r}
    {K : Set (Frame Ψ r)} (hβ : ContinuousOn β K) : ContinuousOn (fun y => rmul y (β y)) K := by sorry
