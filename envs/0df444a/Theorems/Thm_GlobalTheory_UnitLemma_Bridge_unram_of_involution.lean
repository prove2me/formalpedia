-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Bridge_unram_of_involution
-- name    : GlobalTheory.UnitLemma.Bridge.unram_of_involution
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:26:18.670811+00:00
-- url     : https://prove2.me/theorems/f4f7d8bc-f224-4421-863d-21711059c2e2
-- title:
--   Bridge: unram of involution
-- statement:
--   The Bridge construction uses the unram of involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L50-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/LocallyCompactOfComplete.lean#L50-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LocallyCompactOfComplete
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Bridge

theorem GlobalTheory.UnitLemma.Bridge.unram_of_involution {E : Type} [nE : NontriviallyNormedField E] [CharZero E] [IsUltrametricDist E]
    [LocallyCompactSpace E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (hne : ∃ y, c y ≠ y)
    (hn : ∀ y, ‖c y‖ = ‖y‖) (hu : ∀ y : E, ∃ x, c x = x ∧ ‖y‖ = ‖x‖) :
    ∃ (F : Type) (_ : NontriviallyNormedField F) (_ : NormedAlgebra F E) (st : StarRing E),
      GlobalTheory.JR.Unram F E ∧ ∀ y, st.star y = c y := by sorry
