-- Prove2me | Theorems.Thm_GlobalTheory_UnipotentBorder_udl_unique
-- name    : GlobalTheory.UnipotentBorder.udl_unique
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:25:31.303731+00:00
-- url     : https://prove2.me/theorems/c5612ce5-774f-4383-b20b-02dbb73eddc6
-- title:
--   Unipotent Border: udl unique
-- statement:
--   The Unipotent Border construction uses the udl unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L60-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IwahoriFactorisation.lean#L60-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnipotentBorder
open Matrix
variable {O : Type} [CommRing O]

theorem GlobalTheory.UnipotentBorder.udl_unique : ∀ (n : ℕ) (U U' L L' : Matrix (Fin n) (Fin n) O) (D D' : Fin n → Oˣ),
    IsUU U → IsUU U' → IsLU L → IsLU L' →
    U * diagonal (fun i => (D i : O)) * L = U' * diagonal (fun i => (D' i : O)) * L' →
    U = U' ∧ D = D' ∧ L = L' := by sorry
