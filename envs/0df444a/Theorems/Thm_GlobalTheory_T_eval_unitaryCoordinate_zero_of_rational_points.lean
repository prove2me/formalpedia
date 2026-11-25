-- Prove2me | Theorems.Thm_GlobalTheory_T_eval_unitaryCoordinate_zero_of_rational_points
-- name    : GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:46.562803+00:00
-- url     : https://prove2.me/theorems/5752e08e-43aa-4781-9825-6e6aa07ca33d
-- title:
--   T: eval unitary Coordinate zero of rational points
-- statement:
--   The T construction uses the eval unitary Coordinate zero of rational points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvalUnitaryCoordinateZeroOfRationalPointsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvalUnitaryCoordinateZeroOfRationalPointsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.eval_unitaryCoordinate_zero_of_rational_points : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ), (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) → ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by sorry
