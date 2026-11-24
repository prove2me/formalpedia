-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_tauPt_mul
-- name    : GlobalTheory.AlgWtHW.tauPt_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:14.669291+00:00
-- url     : https://prove2.me/theorems/fd5822cd-3d0a-47e0-83dd-24b08b754299
-- title:
--   Alg Wt HW: tau Pt mul
-- statement:
--   The Alg Wt HW construction uses the tau Pt mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean#L19-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanRationalPointOrbitAlgebraicWeightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem GlobalTheory.AlgWtHW.tauPt_mul (τ : L →+* ℂ) (A B : GL (Fin n) ℂ) :
    tauPt τ (A * B) = fun σ => tauPt τ A σ * tauPt τ B σ := by sorry
