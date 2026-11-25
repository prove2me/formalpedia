-- Prove2me | Theorems.Thm_GlobalTheory_posDef_compoundMatrix
-- name    : GlobalTheory.posDef_compoundMatrix
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:55:09.226805+00:00
-- url     : https://prove2.me/theorems/b6dd015f-56aa-4b68-b5a4-77dab023119d
-- title:
--   Global Theory: pos Def compound Matrix
-- statement:
--   The Global Theory construction uses the pos Def compound Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L578-L586
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/SmulOneLeAndLeSmulOneIffEigenvalues.lean#L578-L586

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_StarInvMulVecDotProductMulVecInvMulVec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_MulConjTransposeEqOneOfOrthonormal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_SmulOneLeAndLeSmulOneIffEigenvalues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Set Filter
open scoped ComplexOrder MatrixOrder Kronecker Topology
open GlobalTheory
variable {l n o : Type*} [LinearOrder l] [LinearOrder n] [LinearOrder o]
variable [Fintype n]

theorem GlobalTheory.posDef_compoundMatrix (k : ℕ) {G : Matrix n n ℂ} (hG : G.PosDef) :
    (compoundMatrix k G).PosDef := by sorry
