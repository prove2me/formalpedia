-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_exists_mem_ne_zero
-- name    : GlobalTheory.ThetaTranslJet.exists_mem_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:23:04.296713+00:00
-- url     : https://prove2.me/theorems/b02b7a53-26bf-4454-8dc0-c0083f32ec59
-- title:
--   Theta Transl Jet: exists mem ne zero
-- statement:
--   The Theta Transl Jet construction uses the exists mem ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L300-L323
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L300-L323

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

theorem GlobalTheory.ThetaTranslJet.exists_mem_ne_zero {σ V : Type} [Fintype σ] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {n : ℕ} (P : MvPolynomial σ ℂ) (u : σ → Fin n → V) (T : Set (V → ℂ))
    (hT : ∀ G ∈ T, Differentiable ℂ G) (F : Fin n → V → ℂ) (hF : ∀ b, F b ∈ Submodule.span ℂ T)
    (h : polyDeriv P u (fun z => ∏ b, F b (z b)) 0 ≠ 0) :
    ∃ G : Fin n → V → ℂ, (∀ b, G b ∈ T) ∧ polyDeriv P u (fun z => ∏ b, G b (z b)) 0 ≠ 0 := by sorry
