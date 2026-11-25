-- Prove2me | Theorems.Thm_GlobalTheory_KTypeCompare_isKTypeOf_iff
-- name    : GlobalTheory.KTypeCompare.isKTypeOf_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T02:58:31.875623+00:00
-- url     : https://prove2.me/theorems/bc64dae2-d953-4777-b9e7-a2716fb02e46
-- title:
--   KType Compare: is KType Of iff
-- statement:
--   The KType Compare construction uses the is KType Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L124-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/IsWtOnIffOfTorus.lean#L124-L132

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem GlobalTheory.KTypeCompare.isKTypeOf_iff (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (Λ : Fin n → ℝ) (S : Submodule ℂ H) :
    PI.UpqRep.IsKTypeOf ε σ Λ S ↔ HarishChandraRootData.IsKType ε σ S Λ := by sorry
