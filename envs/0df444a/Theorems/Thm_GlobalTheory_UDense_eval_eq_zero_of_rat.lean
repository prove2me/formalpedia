-- Prove2me | Theorems.Thm_GlobalTheory_UDense_eval_eq_zero_of_rat
-- name    : GlobalTheory.UDense.eval_eq_zero_of_rat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:18:00.532372+00:00
-- url     : https://prove2.me/theorems/1ff04941-c1ce-4304-9191-9d4112ef041f
-- title:
--   UDense: eval eq zero of rat
-- statement:
--   The UDense construction uses the eval eq zero of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvalUnitaryCoordinateZeroOfRationalPoints.lean#L105-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/EvalUnitaryCoordinateZeroOfRationalPoints.lean#L105-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialClearDenominatorsEvalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CayleyTransformMemRationalUnitaryGroupStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamilyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPoints
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
open GlobalTheory GlobalTheory.UDense

theorem GlobalTheory.UDense.eval_eq_zero_of_rat : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (F : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    (∀ γ₀ : GL (Fin n) L, γ₀ ∈ GQ0 L n → MvPolynomial.eval (upt (ratPt (γ₀ : Matrix (Fin n) (Fin n) L))) F = 0) →
    ∀ X : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → MvPolynomial.eval (upt X) F = 0 := by sorry
