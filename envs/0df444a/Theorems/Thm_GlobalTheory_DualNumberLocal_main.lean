-- Prove2me | Theorems.Thm_GlobalTheory_DualNumberLocal_main
-- name    : GlobalTheory.DualNumberLocal.main
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:30.134829+00:00
-- url     : https://prove2.me/theorems/30fb1b91-0cec-474c-a930-6bfe03242deb
-- title:
--   Dual Number Local: main
-- statement:
--   The Dual Number Local construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsRest.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ImportsRest.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Matrix
open GlobalTheory GlobalTheory.DualNumberLocal

theorem GlobalTheory.DualNumberLocal.main : ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O], ∃ _ : IsLocalRing (DualNumber O), IsNoetherianRing (DualNumber O) ∧ IsAdicComplete (maximalIdeal (DualNumber O)) (DualNumber O) ∧ IsLocalHom (algebraMap O (DualNumber O)) ∧ Function.Surjective (fun x : O => residue (DualNumber O) (algebraMap O (DualNumber O) x)) ∧ ∀ z : DualNumber O, z ∈ maximalIdeal (DualNumber O) ↔ z.fst ∈ maximalIdeal O := by sorry
