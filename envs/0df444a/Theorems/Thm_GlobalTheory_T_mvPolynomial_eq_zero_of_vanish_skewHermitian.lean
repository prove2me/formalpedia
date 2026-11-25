-- Prove2me | Theorems.Thm_GlobalTheory_T_mvPolynomial_eq_zero_of_vanish_skewHermitian
-- name    : GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:59.64805+00:00
-- url     : https://prove2.me/theorems/08a110ad-f08c-554c-8f9c-840049519a8d
-- title:
--   T: mv Polynomial eq zero of vanish skew Hermitian
-- statement:
--   The T construction uses the mv Polynomial eq zero of vanish skew Hermitian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitianStatement.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitianStatement.lean#L9-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitianStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.mvPolynomial_eq_zero_of_vanish_skewHermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → σ ≠ AlgHom.id F E → Module.finrank F E = 2 →
    ∀ {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ)), Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), Formalism.UG.cT (σ : E →+* E) J = J → J.det ≠ 0 →
    ∀ Q : MvPolynomial (ι × Fin n × Fin n) ℂ,
      (∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) → Q = 0 := by sorry
