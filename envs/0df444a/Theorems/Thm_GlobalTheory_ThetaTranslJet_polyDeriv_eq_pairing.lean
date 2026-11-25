-- Prove2me | Theorems.Thm_GlobalTheory_ThetaTranslJet_polyDeriv_eq_pairing
-- name    : GlobalTheory.ThetaTranslJet.polyDeriv_eq_pairing
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:32.063982+00:00
-- url     : https://prove2.me/theorems/d87dd660-46cf-4623-b9b0-133ad3c0e03e
-- title:
--   Theta Transl Jet: poly Deriv eq pairing
-- statement:
--   The Theta Transl Jet construction uses the poly Deriv eq pairing property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L43-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ThetaFunctionIsogenyRestriction.lean#L43-L47

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

theorem GlobalTheory.ThetaTranslJet.polyDeriv_eq_pairing {σ W : Type} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (F : W → ℂ) :
    polyDeriv P u F 0 = pairing P (taylorDir u F) := by sorry
