-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_finite_algebra_splitting_normForm
-- name    : GlobalTheory.T.exists_finite_algebra_splitting_normForm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:26.570795+00:00
-- url     : https://prove2.me/theorems/db9c3ec5-1f0d-4847-9bdf-fde8bdb7b80c
-- title:
--   T: exists finite algebra splitting norm Form
-- statement:
--   The T construction uses the exists finite algebra splitting norm Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteAlgebraSplittingNormFormStatement.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFiniteAlgebraSplittingNormFormStatement.lean#L7-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteAlgebraSplittingNormForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteAlgebraSplittingNormFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_finite_algebra_splitting_normForm : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ →
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra A R), Function.Injective (algebraMap A R) ∧ Module.Finite A R ∧
      ∃ σ : Fin (Module.finrank K L) → (B →+* R), (∀ j, (σ j).comp φ = algebraMap A R) ∧
        ∀ (m : ℕ) (g : Fin m → B), ∃ P : MvPolynomial (Fin m) A,
          P.map (algebraMap A K) = GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i)) ∧
          P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i := by sorry
