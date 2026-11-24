-- Prove2me | Theorems.Thm_GlobalTheory_AlgWtHW_eval_upt_eq_zero_of_skew
-- name    : GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:56:51.510967+00:00
-- url     : https://prove2.me/theorems/4f61a3cb-ccd7-4704-9ef9-42bda6ad48de
-- title:
--   Alg Wt HW: eval upt eq zero of skew
-- statement:
--   The Alg Wt HW construction uses the eval upt eq zero of skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialEvalZeroOfVanishingRationalSkewHermi.lean#L7-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/MvPolynomialEvalZeroOfVanishingRationalSkewHermi.lean#L7-L114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolyRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_MvPolynomialEvalZeroOfVanishingRationalSkewHermi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
open GlobalTheory GlobalTheory.AlgWtHW

theorem GlobalTheory.AlgWtHW.eval_upt_eq_zero_of_skew (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (Q : MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) L, S + (S.map (IsCMField.complexConj L : L →+* L))ᵀ = 0 →
      MvPolynomial.eval (upt (ratPt S)) Q = 0)
    (Y : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ σ, Y (ComplexEmbedding.conjugate σ) = -(Y σ)ᵀ) :
    MvPolynomial.eval (upt Y) Q = 0 := by sorry
