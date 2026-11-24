-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_isPolyRep_evPt
-- name    : GlobalTheory.AlgWtHW.isPolyRep_evPt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:58:25.836799+00:00
-- url     : https://prove2.me/theorems/178eb427-8053-4cd8-85fb-937b285ecd68
-- title:
--   Alg Wt HW: is Poly Rep ev Pt
-- statement:
--   The Alg Wt HW construction uses the is Poly Rep ev Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean#L49-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean#L49-L65

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

theorem GlobalTheory.AlgWtHW.isPolyRep_evPt (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type)
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (h : Agrees a b P) (τ : L →+* ℂ) :
    IsPolyRep (fun B => evM P (evPt τ B)) := by sorry
