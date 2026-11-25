-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_sum_mul_repr_single
-- name    : GlobalTheory.AdLat.sum_mul_repr_single
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:55:36.48767+00:00
-- url     : https://prove2.me/theorems/42a19cfa-2480-4b3f-9cf9-55e45c3af3d2
-- title:
--   Ad Lat: sum mul repr single
-- statement:
--   The Ad Lat construction uses the sum mul repr single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemAdelicCompletionPseudoBasisIff.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/MemAdelicCompletionPseudoBasisIff.lean#L19-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MemAdelicCompletionPseudoBasisIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdLat
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix nonZeroDivisors
variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.AdLat.sum_mul_repr_single (e : Module.Basis (Fin n) E (Fin n → E)) (x : Fin n → E) (b : Fin n) :
    ∑ i, x i * e.repr (Pi.single i 1) b = e.repr x b := by sorry
