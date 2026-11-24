-- Prove2me | Theorems.Thm_GlobalTheory_OrdMul_coeff_mem_of_pow_mul
-- name    : GlobalTheory.OrdMul.coeff_mem_of_pow_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:18.086129+00:00
-- url     : https://prove2.me/theorems/5a45e47a-3fa9-466e-957a-27143b3c5d7a
-- title:
--   Ord Mul: coeff mem of pow mul
-- statement:
--   The Ord Mul construction uses the coeff mem of pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffMemOfPowMul.lean#L81-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffMemOfPowMul.lean#L81-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CoeffMemOfPowMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrdMul
open MvPolynomial

theorem GlobalTheory.OrdMul.coeff_mem_of_pow_mul : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by sorry
