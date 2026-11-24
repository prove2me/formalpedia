-- Prove2me | Theorems.Thm_GlobalTheory_CMModel_exists_prime_natCast_mem_pow_of_ringHom
-- name    : GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:02:48.950935+00:00
-- url     : https://prove2.me/theorems/34bde7e7-3ccb-4db8-9f7d-f9c6eb7f3862
-- title:
--   CMModel: exists prime nat Cast mem pow of ring Hom
-- statement:
--   The CMModel construction uses the exists prime nat Cast mem pow of ring Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeNatCastMemPowOfRingHom.lean#L6-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPrimeNatCastMemPowOfRingHom.lean#L6-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimeNatCastMemPowOfRingHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMModel

theorem GlobalTheory.CMModel.exists_prime_natCast_mem_pow_of_ringHom :
    ∀ (F H : Type) [Field F] [NumberField F] [Field H] [NumberField H] (f : F →+* H) (w : HeightOneSpectrum (𝓞 F)) (p n : ℕ), (p : 𝓞 F) ∈ w.asIdeal ^ n → ∃ P : Ideal (𝓞 H), P.IsPrime ∧ P ≠ ⊥ ∧ (p : 𝓞 H) ∈ P ^ n := by sorry
