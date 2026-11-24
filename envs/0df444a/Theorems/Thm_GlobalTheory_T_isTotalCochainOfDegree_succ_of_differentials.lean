-- Prove2me | Theorems.Thm_GlobalTheory_T_isTotalCochainOfDegree_succ_of_differentials
-- name    : GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:50:59.983918+00:00
-- url     : https://prove2.me/theorems/4d5d87bd-e2c7-4152-a26b-bf4b85999dad
-- title:
--   T: is Total Cochain Of Degree succ of differentials
-- statement:
--   The T construction uses the is Total Cochain Of Degree succ of differentials property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsTotalCochainOfDegreeSuccOfDifferentialsStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsTotalCochainOfDegreeSuccOfDifferentialsStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentials
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsTotalCochainOfDegreeSuccOfDifferentialsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isTotalCochainOfDegree_succ_of_differentials : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E), (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → ∀ m c, InTot T m c → InTot T (m + 1) (delta c) ∧ ((∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → InTot T (m + 1) (Dtot d c)) := by sorry
