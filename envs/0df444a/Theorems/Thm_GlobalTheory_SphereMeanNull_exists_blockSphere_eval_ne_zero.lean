-- Prove2me | Theorems.Thm_GlobalTheory_SphereMeanNull_exists_blockSphere_eval_ne_zero
-- name    : GlobalTheory.SphereMeanNull.exists_blockSphere_eval_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:20:05.353573+00:00
-- url     : https://prove2.me/theorems/b40234f3-8c2e-4d7b-8b5f-6d53a99230b9
-- title:
--   Sphere Mean Null: exists block Sphere eval ne zero
-- statement:
--   The Sphere Mean Null construction uses the exists block Sphere eval ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BlockSphereProbZeroSetEqZero.lean#L11-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BlockSphereProbZeroSetEqZero.lean#L11-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFirstCoords
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BlockSphereProbZeroSetEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
noncomputable section
open GlobalTheory GlobalTheory.SphereMeanNull

theorem GlobalTheory.SphereMeanNull.exists_blockSphere_eval_ne_zero {B n : ℕ} (hn : 0 < n) {a : Fin B → ℕ}
    {g : MvPolynomial (Fin B × Fin n) ℂ} (hg0 : g ≠ 0) (hg : IsMultiHomogeneous a g) :
    ∃ u : BlockSphere B n, eval (blockPoint u) g ≠ 0 := by sorry
