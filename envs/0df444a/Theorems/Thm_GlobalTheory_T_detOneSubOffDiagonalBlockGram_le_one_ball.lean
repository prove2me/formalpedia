-- Prove2me | Theorems.Thm_GlobalTheory_T_detOneSubOffDiagonalBlockGram_le_one_ball
-- name    : GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:01.787887+00:00
-- url     : https://prove2.me/theorems/a1f52d12-18c0-516e-964e-3dc3001ad5ff
-- title:
--   T: det One Sub Off Diagonal Block Gram le one ball
-- statement:
--   The T construction uses the det One Sub Off Diagonal Block Gram le one ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetOneSubOffDiagonalBlockGramLeOneBallStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DetOneSubOffDiagonalBlockGramLeOneBallStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBall
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_PoincareCuspForms_ExhaustionFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DetOneSubOffDiagonalBlockGramLeOneBallStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.detOneSubOffDiagonalBlockGram_le_one_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (X.p0 = 1 ∨ X.p0 + 1 = r) → ∀ z : V (nd X), z ∈ Om X → ∀ τ : X.Ψ, zDet X z τ ≤ 1 := by sorry
