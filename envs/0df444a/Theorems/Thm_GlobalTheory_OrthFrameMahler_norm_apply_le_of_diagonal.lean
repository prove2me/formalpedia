-- Prove2me | Theorems.Thm_GlobalTheory_OrthFrameMahler_norm_apply_le_of_diagonal
-- name    : GlobalTheory.OrthFrameMahler.norm_apply_le_of_diagonal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:18:45.654698+00:00
-- url     : https://prove2.me/theorems/e8aedf3c-13d9-45b0-afd6-651ea14996ed
-- title:
--   Orth Frame Mahler: norm apply le of diagonal
-- statement:
--   The Orth Frame Mahler construction uses the norm apply le of diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBoundOrthonormalFrameMahler.lean#L25-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsBoundOrthonormalFrameMahler.lean#L25-L36

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

theorem GlobalTheory.OrthFrameMahler.norm_apply_le_of_diagonal {Ψ : Finset (E →+* ℂ)} {r : ℕ} (z t : Frame Ψ r)
    (hdiag : ∀ τ a, ‖t τ a a‖ = 1 ∧ ∀ c, c ≠ a → t τ a c = 0) (τ : Ψ) (a c : Fin r) :
    ‖z τ a c‖ ≤ ‖rmul z t‖ := by sorry
