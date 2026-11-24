-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtMul_eval_bind_substL
-- name    : GlobalTheory.AlgWtMul.eval_bind_substL
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:56:49.987798+00:00
-- url     : https://prove2.me/theorems/b5aac844-1c37-4a65-b016-fb2b0edab290
-- title:
--   Alg Wt Mul: eval bind subst L
-- statement:
--   The Alg Wt Mul construction uses the eval bind subst L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L20-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L20-L32

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

theorem GlobalTheory.AlgWtMul.eval_bind_substL (A Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) :
    MvPolynomial.eval (upt Y) (MvPolynomial.bind₁ (substL A) Q) =
      MvPolynomial.eval (upt (fun σ => A σ * Y σ)) Q := by sorry
