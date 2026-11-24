-- Prove2me | Theorems.Thm_GordanGenProof_gcone_sub
-- name    : GordanGenProof.gcone_sub
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:25:14.521522+00:00
-- url     : https://prove2.me/theorems/7011c47b-714b-4abe-8cce-252d72c32485
-- title:
--   Gordan Gen Proof: gcone sub
-- statement:
--   The Gordan Gen Proof construction uses the gcone sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GordanIntegerMultiple/ExistsIntMultiple.lean#L16-L22

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_GordanCones
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GordanIntegerMultiple_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GordanGenProof
open Finset

theorem GordanGenProof.gcone_sub {n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Fin n → ℚ) (X : Set (Fin n → ℚ))
    (h0 : (0 : Fin n → ℚ) ∈ X) (hadd : ∀ x ∈ X, ∀ y ∈ X, x + y ∈ X)
    (hsmul : ∀ r : ℚ, 0 ≤ r → ∀ x ∈ X, r • x ∈ X) (hf : ∀ i ∈ s, f i ∈ X) :
    gcone s f ⊆ X := by sorry
