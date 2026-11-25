-- Prove2me | Theorems.Thm_GlobalTheory_omega_eq_zero_of_p_smul_eq_zero
-- name    : GlobalTheory.omega_eq_zero_of_p_smul_eq_zero
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T02:56:01.46399+00:00
-- url     : https://prove2.me/theorems/2ec7addc-6c22-58f8-a740-87faf3e30fa1
-- title:
--   Global Theory: omega eq zero of p smul eq zero
-- statement:
--   The Global Theory construction uses the omega eq zero of p smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupOmegaNoPTorsionOfCotangentInjective.lean#L8-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PDivGroupOmegaNoPTorsionOfCotangentInjective.lean#L8-L18

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupOmegaNoPTorsionOfCotangentInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open PDiv

theorem GlobalTheory.omega_eq_zero_of_p_smul_eq_zero :
    ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R),
      (∀ n, Function.Injective (GlobalTheory.PDiv.cotMap (G.mulP n))) →
        ∀ w : G.omega, (p : R) • w = 0 → w = 0 := by sorry
