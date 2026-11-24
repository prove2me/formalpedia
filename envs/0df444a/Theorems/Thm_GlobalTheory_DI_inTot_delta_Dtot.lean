-- Prove2me | Theorems.Thm_GlobalTheory_DI_inTot_delta_Dtot
-- name    : GlobalTheory.DI.inTot_delta_Dtot
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:06.539111+00:00
-- url     : https://prove2.me/theorems/8594e2c1-2395-4f30-ba3c-bb586ccd096d
-- title:
--   DI: in Tot delta Dtot
-- statement:
--   The DI construction uses the in Tot delta Dtot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsTotalCochainOfDegreeSuccOfDifferentials.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsTotalCochainOfDegreeSuccOfDifferentials.lean#L6-L45

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentials
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI

theorem GlobalTheory.DI.inTot_delta_Dtot : ∀ {ι : Type} [LinearOrder ι] {E : Type}
    [AddCommGroup E] (d : E →+ E)
    (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) →
    ∀ m c, _root_.GlobalTheory.DI.InTot T m c → _root_.GlobalTheory.DI.InTot T (m + 1)
        (_root_.GlobalTheory.DI.delta c) ∧
      ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) →
        _root_.GlobalTheory.DI.InTot T (m + 1) (_root_.GlobalTheory.DI.Dtot d c)) := by sorry
