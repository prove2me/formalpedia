-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_pairing_ne_zero
-- name    : GlobalTheory.ThetaTranslJet.exists_pairing_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:13.467179+00:00
-- url     : https://prove2.me/theorems/2614fe70-be3f-4167-a94c-0363630c6346
-- title:
--   Theta Transl Jet: exists pairing ne zero
-- statement:
--   The Theta Transl Jet construction uses the exists pairing ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L56-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L56-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_CoeffEqZeroOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ImFormApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ThetaFunctionIsogenyRestriction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ReciprocityTheory.ChartRestriction.G.I2
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaTranslJet

theorem GlobalTheory.ThetaTranslJet.exists_pairing_ne_zero {σ : Type} [Fintype σ] {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ x ∈ germIdeal σ ℂ ^ P.totalDegree, pairing P x ≠ 0 := by sorry
