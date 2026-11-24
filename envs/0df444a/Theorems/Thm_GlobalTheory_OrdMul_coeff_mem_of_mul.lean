-- Prove2me | Theorems.Thm_GlobalTheory_OrdMul_coeff_mem_of_mul
-- name    : GlobalTheory.OrdMul.coeff_mem_of_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:38:19.099472+00:00
-- url     : https://prove2.me/theorems/59d2c4ef-ae0e-403e-8571-7f70d4bcdac3
-- title:
--   Ord Mul: coeff mem of mul
-- statement:
--   The Ord Mul construction uses the coeff mem of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffMemOfPowMul.lean#L7-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CoeffMemOfPowMul.lean#L7-L79

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

theorem GlobalTheory.OrdMul.coeff_mem_of_mul {O : Type} [CommRing O] (I : Ideal O) {ι : Type} (K : Set ι) (q : ι)
    (hq : q ∉ K) (a F : MvPolynomial ι O) (N : ℕ) (h0 : a.coeff 0 = 0)
    (hu : IsUnit (a.coeff (Finsupp.single q 1)))
    (H : ∀ m : ι →₀ ℕ, m.degree < N + 1 → (∀ j ∈ K, m j = 0) → (a * F).coeff m ∈ I) :
    ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by sorry
