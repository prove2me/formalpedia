-- Prove2me | Theorems.Thm_GlobalTheory_fixedField_ker_toPerm_finite_isGalois_finrank_dvd
-- name    : GlobalTheory.fixedField_ker_toPerm_finite_isGalois_finrank_dvd
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:45:58.016796+00:00
-- url     : https://prove2.me/theorems/762c7fac-eda8-4c45-ab91-383e3ec1c350
-- title:
--   Global Theory: fixed Field ker to Perm finite is Galois finrank dvd
-- statement:
--   The Global Theory construction uses the fixed Field ker to Perm finite is Galois finrank dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedFieldKerToPermFiniteIsGaloisFinrankDvd.lean#L7-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FixedFieldKerToPermFiniteIsGaloisFinrankDvd.lean#L7-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FixedFieldKerToPermFiniteIsGaloisFinrankDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IntermediateField
open GlobalTheory

theorem GlobalTheory.fixedField_ker_toPerm_finite_isGalois_finrank_dvd (Ω K : Type) [Field Ω] [Field K]
    [Algebra Ω K] [IsAlgClosure Ω K] [CharZero Ω] (n : ℕ)
    (φ : (K ≃ₐ[Ω] K) →* Equiv.Perm (Fin n)) :
    FiniteDimensional Ω (IntermediateField.fixedField φ.ker) ∧
      IsGalois Ω (IntermediateField.fixedField φ.ker) ∧
      Module.finrank Ω (IntermediateField.fixedField φ.ker) ∣ n.factorial := by sorry
