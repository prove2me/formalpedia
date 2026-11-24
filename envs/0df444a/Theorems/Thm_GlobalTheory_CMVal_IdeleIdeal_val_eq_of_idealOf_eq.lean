-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_val_eq_of_idealOf_eq
-- name    : GlobalTheory.CMVal.IdeleIdeal.val_eq_of_idealOf_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:03.030386+00:00
-- url     : https://prove2.me/theorems/465a7126-fceb-4949-a914-eece683d02bf
-- title:
--   Idele Ideal: val eq of ideal Of eq
-- statement:
--   The Idele Ideal construction uses the val eq of ideal Of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L61-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L61-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.IdeleIdeal.val_eq_of_idealOf_eq {y y' : (Af E)ˣ} (h : ∀ w, Valued.v ((y : Af E) w) ≤ 1)
    (h' : ∀ w, Valued.v ((y' : Af E) w) ≤ 1) (e : idealOf y = idealOf y') (w : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) w) = Valued.v ((y' : Af E) w) := by sorry
