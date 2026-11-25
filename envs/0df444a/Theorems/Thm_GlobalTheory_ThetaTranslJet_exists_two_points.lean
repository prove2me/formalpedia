-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_two_points
-- name    : GlobalTheory.ThetaTranslJet.exists_two_points
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:24:13.534797+00:00
-- url     : https://prove2.me/theorems/50401972-abe2-4028-b6ea-06022d1ed1bf
-- title:
--   Theta Transl Jet: exists two points
-- statement:
--   The Theta Transl Jet construction uses the exists two points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L242-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L242-L256

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
variable {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ}

theorem GlobalTheory.ThetaTranslJet.exists_two_points {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0)
    (T : Fin g → ℂ) {p : ℕ} (hp : p ≠ 0) : ∃ c, θ c ≠ 0 ∧ θ (T - p • c) ≠ 0 := by sorry
