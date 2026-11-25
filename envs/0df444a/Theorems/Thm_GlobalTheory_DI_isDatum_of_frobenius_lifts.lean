-- Prove2me | Theorems.Thm_GlobalTheory_DI_isDatum_of_frobenius_lifts
-- name    : GlobalTheory.DI.isDatum_of_frobenius_lifts
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:43.329168+00:00
-- url     : https://prove2.me/theorems/d36a28fb-4347-4f7c-b56d-89fd5d509f8f
-- title:
--   DI: is Datum of frobenius lifts
-- statement:
--   The DI construction uses the is Datum of frobenius lifts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtDAlgebraMapPowCharMul.lean#L42-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtDAlgebraMapPowCharMul.lean#L42-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtDAlgebraMapPowCharMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI

theorem GlobalTheory.DI.isDatum_of_frobenius_lifts {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) {ι : Type} (F : ι → Kt →+* Kt) (d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ])
    (f : ι → Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (h : ι → ι → Ω[K⁄ℤ] →+ K) (hπ : IsFlatLift p π)
    (hF : ∀ i, IsFrob p π (F i)) (hd : IsExtD ℤ K d) (hf : ∀ i, IsF p π (F i) (f i))
    (hh : ∀ i j, IsH p π (F i) (F j) (h i j)) : IsDatum p d f h := by sorry
