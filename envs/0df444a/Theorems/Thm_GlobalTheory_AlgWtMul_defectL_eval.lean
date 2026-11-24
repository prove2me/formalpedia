-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtMul_defectL_eval
-- name    : GlobalTheory.AlgWtMul.defectL_eval
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:57:07.247745+00:00
-- url     : https://prove2.me/theorems/a249072d-41ec-4be5-a33c-76af64275c27
-- title:
--   Alg Wt Mul: defect L eval
-- statement:
--   The Alg Wt Mul construction uses the defect L eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L48-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L48-L54

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

theorem GlobalTheory.AlgWtMul.defectL_eval {ι : Type} [Fintype ι] (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (i j : ι) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) (P i j) -
        ∑ m, MvPolynomial.C (evM P (upt A) i m) * P m j) =
      evM P (upt (fun σ => A σ * Y σ)) i j - (evM P (upt A) * evM P (upt Y)) i j := by sorry
