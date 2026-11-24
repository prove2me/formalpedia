-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtMul_ratPt_one
-- name    : GlobalTheory.AlgWtMul.ratPt_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:57:45.37152+00:00
-- url     : https://prove2.me/theorems/e2ae9744-ff39-4561-abe5-39e818f244b5
-- title:
--   Alg Wt Mul: rat Pt one
-- statement:
--   The Alg Wt Mul construction uses the rat Pt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L74-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L74-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
noncomputable section
open GlobalTheory GlobalTheory.AlgWtMul
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem GlobalTheory.AlgWtMul.ratPt_one :
    ratPt ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) := by sorry
