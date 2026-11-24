-- Prove2me | Theorems.Thm_GlobalTheory_CosetCrit_exists_norm_tx_ge
-- name    : GlobalTheory.CosetCrit.exists_norm_tx_ge
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:00:28.283809+00:00
-- url     : https://prove2.me/theorems/8b3c6517-666e-4a12-9a86-f1959ec89c86
-- title:
--   Coset Crit: exists norm tx ge
-- statement:
--   The Coset Crit construction uses the exists norm tx ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TxCosetCriterion.lean#L85-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TxCosetCriterion.lean#L85-L147

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

theorem GlobalTheory.CosetCrit.exists_norm_tx_ge (hI : N.Int q) {n g : ℕ} (hp : n.Prime) (ho : Odd n) (hn : ‖(n : C)‖ = 1)
    (hT : N.Tors n g) {j : ℕ} (hj : 1 ≤ j) (p : N.QT ((n ^ j) ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ)) :
    ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      Real.exp (-(q (p.1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤ ‖N.tx (n ^ j) (p * h)‖ := by sorry
