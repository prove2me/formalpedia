-- Prove2me | Theorems.Thm_GlobalTheory_SkewDense_eq_zero_of_vanish_skew
-- name    : GlobalTheory.SkewDense.eq_zero_of_vanish_skew
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:52:13.812888+00:00
-- url     : https://prove2.me/theorems/b4bd7ce4-562d-4623-a04c-e05d470d935e
-- title:
--   Skew Dense: eq zero of vanish skew
-- statement:
--   The Skew Dense construction uses the eq zero of vanish skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L74-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MvPolynomialEqZeroOfVanishSkewHermitian.lean#L74-L153

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MvPolynomialEqZeroOfVanishSkewHermitian
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
open GlobalTheory GlobalTheory.SkewDense

theorem GlobalTheory.SkewDense.eq_zero_of_vanish_skew (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hσ1 : σ ≠ AlgHom.id F E) (_h2 : Module.finrank F E = 2)
    {ι : Type} [Fintype ι] (ψ : ι → (E →+* ℂ))
    (hψ : Function.Injective (fun τ => (ψ τ).comp (algebraMap F E)))
    (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.cT (σ : E →+* E) J = J) (hdet : J.det ≠ 0)
    (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : ∀ S : Matrix (Fin n) (Fin n) E, Formalism.UG.cT (σ : E →+* E) S * J + J * S = 0 →
        MvPolynomial.eval (fun p => ψ p.1 (S p.2.1 p.2.2)) Q = 0) : Q = 0 := by sorry
