-- Prove2me | Theorems.Thm_GlobalTheory_one_tmul_quotient_eq_zero_iff
-- name    : GlobalTheory.one_tmul_quotient_eq_zero_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:45.443588+00:00
-- url     : https://prove2.me/theorems/af581276-cc3f-47e4-9bd9-1b167abe9adb
-- title:
--   Global Theory: one tmul quotient eq zero iff
-- statement:
--   The Global Theory construction uses the one tmul quotient eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L135-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)

theorem GlobalTheory.one_tmul_quotient_eq_zero_iff (J : Ideal R) {M : Type*} [AddCommGroup M] [Module R M]
    (x : M) : (1 : R ⧸ J) ⊗ₜ[R] x = 0 ↔ x ∈ (J • ⊤ : Submodule R M) := by sorry
