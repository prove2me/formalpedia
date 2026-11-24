-- Prove2me | Theorems.Thm_GlobalTheory_IdealPowerCoefficients_mem_pow_of_coeff
-- name    : GlobalTheory.IdealPowerCoefficients.mem_pow_of_coeff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T17:03:44.696342+00:00
-- url     : https://prove2.me/theorems/08c72532-94f1-4ce8-ae16-d83ac60f74ac
-- title:
--   Ideal Power Coefficients: mem pow of coeff
-- statement:
--   The Ideal Power Coefficients construction uses the mem pow of coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L133-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MemPowIffCoeffMem.lean#L133-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MemPowIffCoeffMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open GlobalTheory GlobalTheory.IdealPowerCoefficients
open MvPowerSeries Finsupp
variable {R : Type u_1} [CommRing R] {κ : Type u_2}

theorem GlobalTheory.IdealPowerCoefficients.mem_pow_of_coeff [Finite κ] (I : Ideal R) (n : ℕ) (f : MvPowerSeries κ R)
    (hf : ∀ e : κ →₀ ℕ, coeff e f ∈ I ^ (n - e.degree)) :
    f ∈ (Ideal.map C I ⊔ Ideal.span (Set.range X)) ^ n := by sorry
