-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtMul_defectR_eval
-- name    : GlobalTheory.AlgWtMul.defectR_eval
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:57:30.010773+00:00
-- url     : https://prove2.me/theorems/dab81cb6-af7a-429d-ae17-7d0d36602461
-- title:
--   Alg Wt Mul: defect R eval
-- statement:
--   The Alg Wt Mul construction uses the defect R eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L56-L62

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

theorem GlobalTheory.AlgWtMul.defectR_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (B X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt X) (MvPolynomial.bind₁ (substR B) (P i j) -
        ∑ m, P i m * MvPolynomial.C (evM P (upt B) m j)) =
      evM P (upt (fun σ => X σ * B σ)) i j - (evM P (upt X) * evM P (upt B)) i j := by sorry
