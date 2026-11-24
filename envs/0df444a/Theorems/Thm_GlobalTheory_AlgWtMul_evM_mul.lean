-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtMul_evM_mul
-- name    : GlobalTheory.AlgWtMul.evM_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:57:47.358414+00:00
-- url     : https://prove2.me/theorems/7f133c69-80c3-45b1-beea-17593df38055
-- title:
--   Alg Wt Mul: ev M mul
-- statement:
--   The Alg Wt Mul construction uses the ev M mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L85-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean#L85-L124

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

theorem GlobalTheory.AlgWtMul.evM_mul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : AlgWt L n) (ι : Type) [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι ℂ a.W) (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ),
    Agrees a b P → evM P (upt (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))) = 1 ∧
      ∀ X Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ, IsUPt X → IsUPt Y →
        evM P (upt (fun σ => X σ * Y σ)) = evM P (upt X) * evM P (upt Y) := by sorry
