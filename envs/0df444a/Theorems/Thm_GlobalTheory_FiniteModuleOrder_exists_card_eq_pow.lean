-- Prove2me | Theorems.Thm_GlobalTheory_FiniteModuleOrder_exists_card_eq_pow
-- name    : GlobalTheory.FiniteModuleOrder.exists_card_eq_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:13:55.04656+00:00
-- url     : https://prove2.me/theorems/be41430e-6230-5ce2-8e0d-4f9aa48a1a74
-- title:
--   Finite Module Order: exists card eq pow
-- statement:
--   The Finite Module Order construction uses the exists card eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEqPowAndIndexGe.lean#L11-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/CardEqPowAndIndexGe.lean#L11-L31

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_CardEqPowAndIndexGe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FiniteModuleOrder

theorem GlobalTheory.FiniteModuleOrder.exists_card_eq_pow (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) :
    ∀ (D : Type) [AddCommGroup D] [Module R D] [Finite D], Nat.card D = n →
      ∃ i : ℕ, Nat.card D = Nat.card (R ⧸ IsLocalRing.maximalIdeal R) ^ i := by sorry
