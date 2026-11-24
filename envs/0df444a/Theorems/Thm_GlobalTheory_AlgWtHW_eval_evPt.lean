-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_eval_evPt
-- name    : GlobalTheory.AlgWtHW.eval_evPt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:57:20.386064+00:00
-- url     : https://prove2.me/theorems/105085c8-6158-497a-8e8e-eac911bf24cb
-- title:
--   Alg Wt HW: eval ev Pt
-- statement:
--   The Alg Wt HW construction uses the eval ev Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean#L36-L47

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

theorem GlobalTheory.AlgWtHW.eval_evPt (τ : L →+* ℂ) (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (B : GL (Fin n) ℂ) :
    MvPolynomial.eval (evPt τ B) Q =
      MvPolynomial.eval (Sum.elim (fun p => B.val p.1 p.2) (fun p => (B⁻¹).val p.1 p.2))
        (MvPolynomial.bind₁ (tauSubst τ) Q) := by sorry
