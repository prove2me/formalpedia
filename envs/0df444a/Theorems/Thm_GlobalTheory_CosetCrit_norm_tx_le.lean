-- Prove2me | Theorems.Thm_GlobalTheory_CosetCrit_norm_tx_le
-- name    : GlobalTheory.CosetCrit.norm_tx_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:27:57.502805+00:00
-- url     : https://prove2.me/theorems/f7f61d34-c98e-4988-a4f6-2b48585875a0
-- title:
--   Coset Crit: norm tx le
-- statement:
--   The Coset Crit construction uses the norm tx le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TxCosetCriterion.lean#L63-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TxCosetCriterion.lean#L63-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsTorsionTwistTsumNormGe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaConstantTermRepresentativeDependenceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTermStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.CosetCrit
variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
omit [CompleteSpace C] [IsAlgClosed C]

theorem GlobalTheory.CosetCrit.norm_tx_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + m • χ₀) ≤ q (p.1.1.toAdd + m • χ)) :
    ‖N.tx m p‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ₀) / (m : ℝ) ^ 2)) := by sorry
