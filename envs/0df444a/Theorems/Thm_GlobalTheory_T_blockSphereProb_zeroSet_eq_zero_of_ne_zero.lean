-- Prove2me | Theorems.Thm_GlobalTheory_T_blockSphereProb_zeroSet_eq_zero_of_ne_zero
-- name    : GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:27:54.057213+00:00
-- url     : https://prove2.me/theorems/8eeec17d-6d91-4541-a95b-3f895d4324cd
-- title:
--   T: block Sphere Prob zero Set eq zero of ne zero
-- statement:
--   The T construction uses the block Sphere Prob zero Set eq zero of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BlockSphereProbZeroSetEqZeroStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BlockSphereProbZeroSetEqZeroStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero : ∀ (B n : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g → blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by sorry
